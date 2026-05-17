import { db, errorLogsTable } from "@workspace/db";
import { errorLogVersionContext } from "./version-context";
import { logger } from "./logger";

type ErrorLogInput = {
  source: "server" | "client";
  level?: "error" | "warn" | "info";
  code?: string | null;
  message: string;
  method?: string | null;
  path?: string | null;
  statusCode?: number | null;
  userId?: string | null;
  clientCommit?: string | null;
  clientVersion?: string | null;
  details?: unknown;
};

function truncate(value: string, max = 1_000): string {
  return value.length > max ? value.slice(0, max) : value;
}

function sanitizeJson(value: unknown, depth = 0): unknown {
  if (value === null || value === undefined) return value ?? null;
  if (typeof value === "string") return truncate(value, 500);
  if (typeof value === "number" || typeof value === "boolean") return value;
  if (Array.isArray(value)) return depth > 2 ? "[array]" : value.slice(0, 20).map((item) => sanitizeJson(item, depth + 1));
  if (typeof value !== "object") return String(value);
  if (depth > 2) return "[object]";
  const blocked = /token|authorization|cookie|passcode|password|secret|ciphertext|wrapped|encryptedKey|recipientEncryptedKeys|nonce|signature/i;
  return Object.fromEntries(
    Object.entries(value as Record<string, unknown>)
      .filter(([key]) => !blocked.test(key))
      .slice(0, 50)
      .map(([key, item]) => [key, sanitizeJson(item, depth + 1)]),
  );
}

export async function recordErrorLog(input: ErrorLogInput): Promise<void> {
  try {
    const version = errorLogVersionContext({ commit: input.clientCommit, version: input.clientVersion });
    await db.insert(errorLogsTable).values({
      source: input.source,
      level: input.level ?? "error",
      code: input.code ?? null,
      message: truncate(input.message),
      method: input.method ?? null,
      path: input.path ?? null,
      statusCode: input.statusCode ?? null,
      userId: input.userId ?? null,
      clientCommit: version.clientCommit,
      clientVersion: version.clientVersion,
      serverCommit: version.serverCommit,
      serverVersion: version.serverVersion,
      serverStartedAt: version.serverStartedAt,
      details: sanitizeJson(input.details),
    });
  } catch (err) {
    logger.warn({ err }, "Failed to persist sanitized error log");
  }
}
