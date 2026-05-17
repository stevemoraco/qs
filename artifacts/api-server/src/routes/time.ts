import { createHmac } from "crypto";
import { Router } from "express";

const router = Router();

const TIME_SOURCES = [
  "https://www.google.com/generate_204",
  "https://www.cloudflare.com/cdn-cgi/trace",
  "https://www.apple.com/library/test/success.html",
  "https://www.microsoft.com",
  "https://www.nist.gov",
  "https://nist.time.gov",
];

function median(values: number[]): number {
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[Math.floor(sorted.length / 2)] ?? Date.now();
}

router.get("/time/attestation", async (_req, res) => {
  const sampledAt = new Date();
  const results = await Promise.all(
    TIME_SOURCES.map(async (url) => {
      try {
        const response = await fetch(url, { method: "HEAD", signal: AbortSignal.timeout(2500) });
        const date = response.headers.get("date");
        const epochMs = date ? Date.parse(date) : Number.NaN;
        return Number.isFinite(epochMs) ? { url, ok: true, epochMs } : { url, ok: false };
      } catch {
        return { url, ok: false };
      }
    }),
  );
  const good = results.filter((result): result is { url: string; ok: true; epochMs: number } => result.ok);
  const synthesizedEpochMs = median(good.map((result) => result.epochMs));
  const payload = {
    version: 1,
    sampledAt: sampledAt.toISOString(),
    synthesizedAt: new Date(synthesizedEpochMs).toISOString(),
    sources: results,
  };
  const signature = createHmac("sha256", process.env["SESSION_SECRET"] ?? "dev-time-attestation")
    .update(JSON.stringify(payload))
    .digest("base64url");
  res.json({ ...payload, signature });
});

export default router;
