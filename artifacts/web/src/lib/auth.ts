const TOKEN_KEY = "qs_token";
const AUTH_HANDLE_KEY = "qs_auth_handle";
const LAST_HANDLE_KEY = "qs_last_handle";
const TOKEN_COOKIE = "qs_token";
const AUTH_HANDLE_COOKIE = "qs_auth_handle";
const LAST_HANDLE_COOKIE = "qs_last_handle";
const DEVICE_PASSCODE_KEY = "qs_device_passcode";
const WEBAUTHN_CREDENTIAL_KEY = "qs_webauthn_credential";
const KEM_SK_KEY = "qs_kem_sk";
const DSA_SK_KEY = "qs_dsa_sk";
const KEM_PK_KEY = "qs_kem_pk";
const DSA_PK_KEY = "qs_dsa_pk";
const COOKIE_MAX_AGE_SECONDS = 60 * 60 * 24 * 400;
const KEY_DB_NAME = "quantumshield-keyring";
const KEY_DB_STORE = "keys";
const KEY_DB_VERSION = 1;

function bytesToBase64(bytes: Uint8Array): string {
  let value = "";
  for (const byte of bytes) value += String.fromCharCode(byte);
  return btoa(value);
}

function base64ToBytes(value: string): Uint8Array {
  return Uint8Array.from(atob(value), (c) => c.charCodeAt(0));
}

function getCookie(name: string): string | null {
  if (typeof document === "undefined") return null;
  const prefix = `${name}=`;
  const value = document.cookie
    .split("; ")
    .find((part) => part.startsWith(prefix))
    ?.slice(prefix.length);
  return value ? decodeURIComponent(value) : null;
}

function setCookie(name: string, value: string): void {
  if (typeof document === "undefined") return;
  const secure = window.location.protocol === "https:" ? "; Secure" : "";
  document.cookie = `${name}=${encodeURIComponent(value)}; Max-Age=${COOKIE_MAX_AGE_SECONDS}; Path=/; SameSite=Lax${secure}`;
}

function clearCookie(name: string): void {
  if (typeof document === "undefined") return;
  const secure = window.location.protocol === "https:" ? "; Secure" : "";
  document.cookie = `${name}=; Max-Age=0; Path=/; SameSite=Lax${secure}`;
}

function getPersistentValue(key: string, cookieName: string): string | null {
  const localValue = localStorage.getItem(key);
  if (localValue) return localValue;
  const cookieValue = getCookie(cookieName);
  if (cookieValue) localStorage.setItem(key, cookieValue);
  return cookieValue;
}

function setPersistentValue(key: string, cookieName: string, value: string): void {
  localStorage.setItem(key, value);
  setCookie(cookieName, value);
}

function clearPersistentValue(key: string, cookieName: string): void {
  localStorage.removeItem(key);
  clearCookie(cookieName);
}

export function getToken(): string | null {
  return getPersistentValue(TOKEN_KEY, TOKEN_COOKIE);
}

export function setToken(token: string): void {
  setPersistentValue(TOKEN_KEY, TOKEN_COOKIE, token);
}

export function getAuthHandle(): string | null {
  return getPersistentValue(AUTH_HANDLE_KEY, AUTH_HANDLE_COOKIE);
}

export function setAuthHandle(authHandle: string): void {
  setPersistentValue(AUTH_HANDLE_KEY, AUTH_HANDLE_COOKIE, authHandle);
}

export function getLastHandle(): string | null {
  return getPersistentValue(LAST_HANDLE_KEY, LAST_HANDLE_COOKIE);
}

export function setLastHandle(handle: string): void {
  setPersistentValue(LAST_HANDLE_KEY, LAST_HANDLE_COOKIE, handle);
}

export function getDevicePasscode(): string | null {
  return localStorage.getItem(DEVICE_PASSCODE_KEY);
}

export function setDevicePasscode(passcode: string): void {
  localStorage.setItem(DEVICE_PASSCODE_KEY, passcode);
}

export function generateDevicePasscode(): string {
  const bytes = new Uint8Array(32);
  crypto.getRandomValues(bytes);
  return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

function credentialIdToBase64(id: ArrayBuffer): string {
  return btoa(String.fromCharCode(...new Uint8Array(id)));
}

function credentialIdFromBase64(id: string): ArrayBuffer {
  const bytes = Uint8Array.from(atob(id), (c) => c.charCodeAt(0));
  return bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
}

export async function enrollDeviceVerification(): Promise<void> {
  if (!window.PublicKeyCredential || !navigator.credentials?.create) {
    throw new Error("Device verification is not available in this browser.");
  }

  const challenge = new Uint8Array(32);
  const userId = new Uint8Array(16);
  crypto.getRandomValues(challenge);
  crypto.getRandomValues(userId);

  const credential = await navigator.credentials.create({
    publicKey: {
      challenge,
      rp: { name: "QuantumShield" },
      user: {
        id: userId,
        name: "quantumshield-device",
        displayName: "QuantumShield Device",
      },
      pubKeyCredParams: [{ type: "public-key", alg: -7 }],
      authenticatorSelection: {
        authenticatorAttachment: "platform",
        residentKey: "preferred",
        userVerification: "required",
      },
      timeout: 60000,
      attestation: "none",
    },
  });

  if (!(credential instanceof PublicKeyCredential)) {
    throw new Error("Device verification was not created.");
  }

  localStorage.setItem(WEBAUTHN_CREDENTIAL_KEY, credentialIdToBase64(credential.rawId));
}

export async function verifyDevice(): Promise<void> {
  if (!window.PublicKeyCredential || !navigator.credentials?.get) {
    throw new Error("Device verification is not available in this browser.");
  }

  const credentialId = localStorage.getItem(WEBAUTHN_CREDENTIAL_KEY);
  if (!credentialId) {
    throw new Error("No device verification is linked to this browser.");
  }

  const challenge = new Uint8Array(32);
  crypto.getRandomValues(challenge);

  await navigator.credentials.get({
    publicKey: {
      challenge,
      allowCredentials: [
        {
          type: "public-key",
          id: credentialIdFromBase64(credentialId),
        },
      ],
      userVerification: "required",
      timeout: 60000,
    },
  });
}

export function clearToken(): void {
  clearPersistentValue(TOKEN_KEY, TOKEN_COOKIE);
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
  localStorage.setItem(KEM_SK_KEY, bytesToBase64(kemSk));
  localStorage.setItem(KEM_PK_KEY, bytesToBase64(kemPk));
  localStorage.setItem(DSA_SK_KEY, bytesToBase64(dsaSk));
  localStorage.setItem(DSA_PK_KEY, bytesToBase64(dsaPk));
  void storeKeyPairInIndexedDb({
    [KEM_SK_KEY]: bytesToBase64(kemSk),
    [KEM_PK_KEY]: bytesToBase64(kemPk),
    [DSA_SK_KEY]: bytesToBase64(dsaSk),
    [DSA_PK_KEY]: bytesToBase64(dsaPk),
  });
}

export function getKemPublicKey(): string | null {
  return localStorage.getItem(KEM_PK_KEY);
}

export function getDsaPublicKey(): string | null {
  return localStorage.getItem(DSA_PK_KEY);
}

export function getLocalKeyPair(): {
  kemSecretKey: Uint8Array | null;
  kemPublicKey: Uint8Array | null;
  dsaSecretKey: Uint8Array | null;
  dsaPublicKey: Uint8Array | null;
} {
  return {
    kemSecretKey: getStoredBytes(KEM_SK_KEY),
    kemPublicKey: getStoredBytes(KEM_PK_KEY),
    dsaSecretKey: getStoredBytes(DSA_SK_KEY),
    dsaPublicKey: getStoredBytes(DSA_PK_KEY),
  };
}

export async function getLocalKeyPairAsync(): Promise<{
  kemSecretKey: Uint8Array | null;
  kemPublicKey: Uint8Array | null;
  dsaSecretKey: Uint8Array | null;
  dsaPublicKey: Uint8Array | null;
}> {
  await hydrateKeyPairFromIndexedDb();
  return getLocalKeyPair();
}

export function getKemSecretKey(): Uint8Array | null {
  return getStoredBytes(KEM_SK_KEY);
}

export async function getKemSecretKeyAsync(): Promise<Uint8Array | null> {
  return getKemSecretKey() ?? (await getStoredBytesAsync(KEM_SK_KEY));
}

export function getDsaSecretKey(): Uint8Array | null {
  return getStoredBytes(DSA_SK_KEY);
}

function getStoredBytes(key: string): Uint8Array | null {
  const v = localStorage.getItem(key);
  if (!v) return null;
  return base64ToBytes(v);
}

async function getStoredBytesAsync(key: string): Promise<Uint8Array | null> {
  await hydrateKeyPairFromIndexedDb();
  return getStoredBytes(key);
}

function openKeyDb(): Promise<IDBDatabase | null> {
  if (typeof indexedDB === "undefined") return Promise.resolve(null);
  return new Promise((resolve) => {
    const req = indexedDB.open(KEY_DB_NAME, KEY_DB_VERSION);
    req.onupgradeneeded = () => {
      req.result.createObjectStore(KEY_DB_STORE);
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => resolve(null);
  });
}

async function storeKeyPairInIndexedDb(values: Record<string, string>): Promise<void> {
  const db = await openKeyDb();
  if (!db) return;
  await new Promise<void>((resolve) => {
    const tx = db.transaction(KEY_DB_STORE, "readwrite");
    for (const [key, value] of Object.entries(values)) tx.objectStore(KEY_DB_STORE).put(value, key);
    tx.oncomplete = () => resolve();
    tx.onerror = () => resolve();
    tx.onabort = () => resolve();
  });
  db.close();
}

export async function hydrateKeyPairFromIndexedDb(): Promise<boolean> {
  const db = await openKeyDb();
  if (!db) return false;
  const keys = [KEM_SK_KEY, KEM_PK_KEY, DSA_SK_KEY, DSA_PK_KEY];
  const values = await new Promise<Record<string, string>>((resolve) => {
    const tx = db.transaction(KEY_DB_STORE, "readonly");
    const store = tx.objectStore(KEY_DB_STORE);
    const found: Record<string, string> = {};
    for (const key of keys) {
      const req = store.get(key);
      req.onsuccess = () => {
        if (typeof req.result === "string" && req.result.length > 0) found[key] = req.result;
      };
    }
    tx.oncomplete = () => resolve(found);
    tx.onerror = () => resolve(found);
    tx.onabort = () => resolve(found);
  });
  db.close();

  let hydrated = false;
  for (const key of keys) {
    if (!localStorage.getItem(key) && values[key]) {
      localStorage.setItem(key, values[key]);
      hydrated = true;
    }
  }
  return hydrated;
}

export function clearAll(): void {
  clearPersistentValue(TOKEN_KEY, TOKEN_COOKIE);
  clearPersistentValue(AUTH_HANDLE_KEY, AUTH_HANDLE_COOKIE);
  clearPersistentValue(LAST_HANDLE_KEY, LAST_HANDLE_COOKIE);
  localStorage.removeItem(DEVICE_PASSCODE_KEY);
  localStorage.removeItem(WEBAUTHN_CREDENTIAL_KEY);
  localStorage.removeItem(KEM_SK_KEY);
  localStorage.removeItem(KEM_PK_KEY);
  localStorage.removeItem(DSA_SK_KEY);
  localStorage.removeItem(DSA_PK_KEY);
  if (typeof indexedDB !== "undefined") indexedDB.deleteDatabase(KEY_DB_NAME);
}

export async function linkDeviceWithInvite(code: string, passcode: string): Promise<{ token: string; authHandle: string }> {
  const res = await fetch("/api/auth/link-device", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      code,
      passcode,
      deviceLabel: navigator.userAgent.slice(0, 80),
    }),
  });

  if (!res.ok) {
    const data = await res.json().catch(() => null) as { error?: string } | null;
    throw new Error(data?.error ?? "Could not link this device with that invite");
  }

  return res.json() as Promise<{ token: string; authHandle: string }>;
}

async function jsonFetch<T>(url: string, body: unknown): Promise<T> {
  const res = await fetch(url, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify(body),
  });
  const data = await res.json().catch(() => null) as T & { error?: string } | null;
  if (!res.ok) {
    throw new Error(data?.error ?? "Request failed");
  }
  return data as T;
}

export async function registerWithPasskey(input: {
  handle: string;
  kemPublicKey: string;
  dsaPublicKey: string;
  leadEmail?: string;
}): Promise<{ token: string; authHandle: string }> {
  const options = await jsonFetch<Parameters<typeof startRegistration>[0]>("/api/auth/passkey/register/options", {
    handle: input.handle,
  });
  const response = await startRegistration(options);
  return jsonFetch<{ token: string; authHandle: string }>("/api/auth/passkey/register/verify", {
    handle: input.handle,
    response,
    kemPublicKey: input.kemPublicKey,
    dsaPublicKey: input.dsaPublicKey,
    leadEmail: input.leadEmail,
  });
}

export async function loginWithPasskey(handle: string): Promise<{ token: string; authHandle: string }> {
  const options = await jsonFetch<Parameters<typeof startAuthentication>[0]>("/api/auth/passkey/login/options", { handle });
  const response = await startAuthentication(options);
  return jsonFetch<{ token: string; authHandle: string }>("/api/auth/passkey/login/verify", {
    handle,
    response,
  });
}
import { startAuthentication, startRegistration } from "@simplewebauthn/browser";
