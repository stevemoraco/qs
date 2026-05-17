import { createHmac } from "crypto";

const TIME_SOURCES = [
  { id: "google", url: "https://www.google.com/generate_204" },
  { id: "cloudflare", url: "https://www.cloudflare.com/cdn-cgi/trace" },
  { id: "apple", url: "https://www.apple.com/library/test/success.html" },
  { id: "microsoft", url: "https://www.microsoft.com" },
  { id: "nist", url: "https://www.nist.gov" },
  { id: "nist-time", url: "https://nist.time.gov" },
];

const MIN_QUORUM_SOURCES = 3;
const MAX_QUORUM_SPREAD_MS = 5 * 60 * 1000;

type SourceResult = {
  id: string;
  url: string;
  ok: boolean;
  epochMs?: number;
};

export type TimeQuorumAttestation = {
  version: 1;
  sampledAt: string;
  serverFallbackEpochMs: number;
  synthesizedAt: string;
  synthesizedEpochMs: number;
  synthesisMode: "quorum_median" | "server_fallback";
  quorumSize: number;
  quorumSpreadMs: number;
  minQuorumSources: number;
  sources: SourceResult[];
  degraded: boolean;
  signature: string;
};

function median(values: number[]): number {
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[Math.floor(sorted.length / 2)] ?? Date.now();
}

function signPayload(payload: Omit<TimeQuorumAttestation, "signature">): string {
  const secret = process.env["TIME_ATTESTATION_SECRET"] ?? process.env["SESSION_SECRET"];
  if (!secret && process.env.NODE_ENV === "production") {
    throw new Error("TIME_ATTESTATION_SECRET or SESSION_SECRET is required in production");
  }
  return createHmac("sha256", secret ?? "dev-time-attestation")
    .update(JSON.stringify(payload))
    .digest("base64url");
}

export async function createTimeQuorumAttestation(): Promise<TimeQuorumAttestation> {
  const sampledAt = new Date();
  const serverFallbackEpochMs = sampledAt.getTime();
  const results = await Promise.all(
    TIME_SOURCES.map(async (source) => {
      try {
        const response = await fetch(source.url, { method: "HEAD", signal: AbortSignal.timeout(2500) });
        const date = response.headers.get("date");
        const epochMs = date ? Date.parse(date) : Number.NaN;
        return Number.isFinite(epochMs)
          ? { id: source.id, url: source.url, ok: true, epochMs }
          : { id: source.id, url: source.url, ok: false };
      } catch {
        return { id: source.id, url: source.url, ok: false };
      }
    }),
  );

  const good = results.filter((result): result is SourceResult & { epochMs: number } => result.ok && typeof result.epochMs === "number");
  const epochs = good.map((result) => result.epochMs);
  const quorumSpreadMs = epochs.length > 0 ? Math.max(...epochs) - Math.min(...epochs) : 0;
  const degraded = good.length < MIN_QUORUM_SOURCES || quorumSpreadMs > MAX_QUORUM_SPREAD_MS;
  // Quorum clock Sybil-hardening: use the public-source median only when enough
  // independent source Date headers agree; otherwise fall back to server time.
  const synthesisMode = degraded ? "server_fallback" : "quorum_median";
  const synthesizedEpochMs = degraded ? serverFallbackEpochMs : median(epochs);
  const payload: Omit<TimeQuorumAttestation, "signature"> = {
    version: 1,
    sampledAt: sampledAt.toISOString(),
    serverFallbackEpochMs,
    synthesizedAt: new Date(synthesizedEpochMs).toISOString(),
    synthesizedEpochMs,
    synthesisMode,
    quorumSize: good.length,
    quorumSpreadMs,
    minQuorumSources: MIN_QUORUM_SOURCES,
    sources: results,
    degraded,
  };
  return { ...payload, signature: signPayload(payload) };
}
