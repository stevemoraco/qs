import { db, errorLogsTable } from "@workspace/db";
import { sql } from "drizzle-orm";
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

let ensureErrorLogsTablePromise: Promise<void> | null = null;

function isMissingErrorLogsTable(err: unknown): boolean {
  const cause = typeof err === "object" && err !== null && "cause" in err
    ? (err as { cause?: unknown }).cause
    : err;
  return typeof cause === "object" && cause !== null && "code" in cause && (cause as { code?: unknown }).code === "42P01";
}

function ensureErrorLogsTable(): Promise<void> {
  ensureErrorLogsTablePromise ??= (async () => {
    await db.execute(sql`
      create table if not exists public.error_logs (
        id uuid primary key default gen_random_uuid(),
        source text not null,
        level text not null default 'error',
        code text,
        message text not null,
        method text,
        path text,
        status_code integer,
        user_id uuid references public.users(id) on delete set null,
        client_commit text,
        client_version text,
        server_commit text,
        server_version text,
        server_started_at timestamptz,
        details jsonb,
        created_at timestamptz not null default now()
      )
    `);
    await db.execute(sql`create index if not exists error_logs_created_at_idx on public.error_logs (created_at desc)`);
    await db.execute(sql`create index if not exists error_logs_code_created_at_idx on public.error_logs (code, created_at desc)`);
    await db.execute(sql`
      create index if not exists error_logs_user_id_created_at_idx
      on public.error_logs (user_id, created_at desc)
      where user_id is not null
    `);
  })().catch((err) => {
    ensureErrorLogsTablePromise = null;
    throw err;
  });
  return ensureErrorLogsTablePromise;
}

async function insertErrorLog(input: ErrorLogInput): Promise<void> {
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
}

export async function recordErrorLog(input: ErrorLogInput): Promise<void> {
  try {
    await insertErrorLog(input);
  } catch (err) {
    if (isMissingErrorLogsTable(err)) {
      try {
        await ensureErrorLogsTable();
        await insertErrorLog(input);
        return;
      } catch (retryErr) {
        logger.warn({ err: retryErr }, "Failed to initialize sanitized error log table");
        return;
      }
    }
    logger.warn({ err }, "Failed to persist sanitized error log");
  }
}
