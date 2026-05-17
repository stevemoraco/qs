import { Router } from "express";
import { recordErrorLog } from "../lib/error-log";
import { optionalAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

function stringField(value: unknown, max = 500): string | null {
  if (typeof value !== "string") return null;
  const trimmed = value.trim();
  if (!trimmed) return null;
  return trimmed.slice(0, max);
}

router.post("/logs/client-error", optionalAuth, async (req: AuthRequest, res) => {
  const body = req.body && typeof req.body === "object" ? req.body as Record<string, unknown> : {};
  const message = stringField(body.message, 1_000);
  if (!message) {
    res.status(400).json({ error: "Error message is required" });
    return;
  }

  await recordErrorLog({
    source: "client",
    level: body.level === "warn" || body.level === "info" ? body.level : "error",
    code: stringField(body.code, 120),
    message,
    method: stringField(body.method, 16),
    path: stringField(body.path, 300),
    statusCode: typeof body.statusCode === "number" ? body.statusCode : null,
    userId: req.userId ?? null,
    clientCommit: stringField(body.clientCommit, 80),
    clientVersion: stringField(body.clientVersion, 120),
    details: body.details,
  });

  res.status(202).json({ ok: true });
});

export default router;
