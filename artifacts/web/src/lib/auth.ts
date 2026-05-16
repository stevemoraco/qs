const TOKEN_KEY = "qs_token";
const KEM_SK_KEY = "qs_kem_sk";
const DSA_SK_KEY = "qs_dsa_sk";
const KEM_PK_KEY = "qs_kem_pk";
const DSA_PK_KEY = "qs_dsa_pk";

export function getToken(): string | null {
  return localStorage.getItem(TOKEN_KEY);
}

export function setToken(token: string): void {
  localStorage.setItem(TOKEN_KEY, token);
}

export function clearToken(): void {
  localStorage.removeItem(TOKEN_KEY);
}

export function isAuthenticated(): boolean {
  return !!getToken();
}

export function storeKeyPair(
  kemSk: Uint8Array,
  kemPk: Uint8Array,
  dsaSk: Uint8Array,
  dsaPk: Uint8Array
): void {
  localStorage.setItem(KEM_SK_KEY, btoa(String.fromCharCode(...kemSk)));
  localStorage.setItem(KEM_PK_KEY, btoa(String.fromCharCode(...kemPk)));
  localStorage.setItem(DSA_SK_KEY, btoa(String.fromCharCode(...dsaSk)));
  localStorage.setItem(DSA_PK_KEY, btoa(String.fromCharCode(...dsaPk)));
}

export function getKemPublicKey(): string | null {
  return localStorage.getItem(KEM_PK_KEY);
}

export function getDsaPublicKey(): string | null {
  return localStorage.getItem(DSA_PK_KEY);
}

export function getKemSecretKey(): Uint8Array | null {
  const v = localStorage.getItem(KEM_SK_KEY);
  if (!v) return null;
  return Uint8Array.from(atob(v), (c) => c.charCodeAt(0));
}

export function getDsaSecretKey(): Uint8Array | null {
  const v = localStorage.getItem(DSA_SK_KEY);
  if (!v) return null;
  return Uint8Array.from(atob(v), (c) => c.charCodeAt(0));
}

export function clearAll(): void {
  localStorage.removeItem(TOKEN_KEY);
  localStorage.removeItem(KEM_SK_KEY);
  localStorage.removeItem(KEM_PK_KEY);
  localStorage.removeItem(DSA_SK_KEY);
  localStorage.removeItem(DSA_PK_KEY);
}
