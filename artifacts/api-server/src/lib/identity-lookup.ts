import { createHash } from "crypto";

const HANDLE_LOOKUP_PEPPER =
  process.env["HANDLE_LOOKUP_PEPPER"] ??
  process.env["SESSION_SECRET"] ??
  "local-development-only-handle-lookup-pepper";

export function normalizeIdentityCode(code: string): string {
  return code.trim().replace(/^[@#]+/, "").toLowerCase();
}

export function isValidIdentityCode(code: string): boolean {
  return /^[a-z0-9][a-z0-9_-]{1,31}$/.test(code);
}

export function isClientLookupHash(code: string): boolean {
  return /^[a-f0-9]{64}$/.test(code);
}

function sha256(value: string): string {
  return createHash("sha256").update(value).digest("hex");
}

function clientLookupHash(codeOrHash: string): string {
  const normalized = normalizeIdentityCode(codeOrHash);
  if (isClientLookupHash(normalized)) return normalized;
  return sha256(`quantumshield-identity-v1:${normalized}`);
}

export function serverLookupCode(codeOrHash: string): string {
  return sha256(`quantumshield-server-lookup-v1:${HANDLE_LOOKUP_PEPPER}:${clientLookupHash(codeOrHash)}`);
}

export function canAcceptIdentityLookupInput(codeOrHash: string): boolean {
  const normalized = normalizeIdentityCode(codeOrHash);
  return isValidIdentityCode(normalized) || isClientLookupHash(normalized);
}

