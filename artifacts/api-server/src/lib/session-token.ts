import { createHash } from "crypto";

export function hashSessionToken(token: string): string {
  return `sha256:${createHash("sha256").update(token).digest("hex")}`;
}

export function sessionTokenLookupValues(token: string): string[] {
  const hashed = hashSessionToken(token);
  return token.startsWith("sha256:") ? [token] : [hashed, token];
}
