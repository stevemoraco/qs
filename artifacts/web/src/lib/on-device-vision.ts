type ThreatDetection = {
  label: string;
  score: number;
  source: "transformers" | "coco-ssd";
};

type Detector = {
  source: ThreatDetection["source"];
  detect(video: HTMLVideoElement): Promise<ThreatDetection[]>;
};

const THREAT_LABELS = new Set(["cell phone", "mobile phone", "phone", "laptop", "tablet", "camera", "webcam"]);
const TRANSFORMERS_MODEL = "onnx-community/rfdetr_small-ONNX";
const FALLBACK_MODEL = "Xenova/detr-resnet-50";

let detectorPromise: Promise<Detector | null> | null = null;

function isThreatLabel(label: string): boolean {
  const normalized = label.toLowerCase();
  return Array.from(THREAT_LABELS).some((threat) => normalized.includes(threat));
}

function frameToDataUrl(video: HTMLVideoElement): string | null {
  const width = video.videoWidth;
  const height = video.videoHeight;
  if (width === 0 || height === 0) return null;

  const canvas = document.createElement("canvas");
  const maxSide = 384;
  const scale = Math.min(1, maxSide / Math.max(width, height));
  canvas.width = Math.max(1, Math.round(width * scale));
  canvas.height = Math.max(1, Math.round(height * scale));

  const ctx = canvas.getContext("2d", { alpha: false });
  if (!ctx) return null;

  ctx.drawImage(video, 0, 0, canvas.width, canvas.height);
  return canvas.toDataURL("image/jpeg", 0.72);
}

async function createTransformersDetector(): Promise<Detector> {
  const { env, pipeline } = await import("@huggingface/transformers");
  env.useBrowserCache = true;
  env.allowRemoteModels = true;
  env.allowLocalModels = false;

  const options = {
    device: "gpu" in navigator ? "webgpu" : "wasm",
    dtype: "q8",
  } as const;

  let pipe: any;
  try {
    pipe = await pipeline("object-detection", TRANSFORMERS_MODEL, options);
  } catch {
    pipe = await pipeline("object-detection", FALLBACK_MODEL, options);
  }

  return {
    source: "transformers",
    async detect(video) {
      const frame = frameToDataUrl(video);
      if (!frame) return [];

      const output = await pipe(frame, { threshold: 0.35, percentage: true });
      return (Array.isArray(output) ? output : [])
        .map((item: { label?: string; score?: number }) => ({
          label: item.label ?? "",
          score: item.score ?? 0,
          source: "transformers" as const,
        }))
        .filter((item) => item.score >= 0.35 && isThreatLabel(item.label));
    },
  };
}

async function createCocoDetector(): Promise<Detector> {
  const cocossd = await import("@tensorflow-models/coco-ssd" as any);
  await import("@tensorflow/tfjs" as any);
  const model = await cocossd.load();

  return {
    source: "coco-ssd",
    async detect(video) {
      const predictions = await model.detect(video);
      return (Array.isArray(predictions) ? predictions : [])
        .map((item: { class?: string; score?: number }) => ({
          label: item.class ?? "",
          score: item.score ?? 0,
          source: "coco-ssd" as const,
        }))
        .filter((item) => item.score >= 0.45 && isThreatLabel(item.label));
    },
  };
}

export async function getFrameThreatDetector(): Promise<Detector | null> {
  detectorPromise ??= (async () => {
    try {
      return await createTransformersDetector();
    } catch {
      try {
        return await createCocoDetector();
      } catch {
        return null;
      }
    }
  })();

  return detectorPromise;
}

