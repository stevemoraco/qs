const TOKEN_KEY = "qs_token";
const AUTH_HANDLE_KEY = "qs_auth_handle";
const LAST_HANDLE_KEY = "qs_last_handle";
const TOKEN_COOKIE = "qs_token";
const AUTH_HANDLE_COOKIE = "qs_auth_handle";
const LAST_HANDLE_COOKIE = "qs_last_handle";
const DEVICE_PASSCODE_KEY = "qs_device_passcode";
const WEBAUTHN_CREDENTIAL_KEY = "qs_webauthn_credential";
const FRESH_LOGIN_VERIFIED_UNTIL_KEY = "qs_fresh_login_verified_until";
const ASSOCIATED_HANDLES_KEY = "qs_associated_handles";
const UNSEALED_HANDLE_LABELS_KEY = "qs_unsealed_handle_labels";
const KEM_SK_KEY = "qs_kem_sk";
const DSA_SK_KEY = "qs_dsa_sk";
const KEM_PK_KEY = "qs_kem_pk";
const DSA_PK_KEY = "qs_dsa_pk";
const HISTORICAL_KEYRING_KEY = "qs_historical_keyring_v1";
const COOKIE_MAX_AGE_SECONDS = 60 * 60 * 24 * 400;
const KEY_DB_NAME = "quantumshield-keyring";
const KEY_DB_STORE = "keys";
const KEY_DB_VERSION = 1;
const PRIVATE_KEY_CACHE_MS = 2 * 60 * 1000;

const privateKeyCache = new Map<string, { value: Uint8Array; expiresAt: number }>();

type HistoricalKeyPair = {
  kemSecretKey: string;
  kemPublicKey: string;
  dsaSecretKey: string;
  dsaPublicKey: string;
  storedAt: string;
};

function isPrivateKey(key: string): boolean {
  return key === KEM_SK_KEY || key === DSA_SK_KEY;
}

function cachePrivateKey(key: string, value: Uint8Array): Uint8Array {
  const previous = privateKeyCache.get(key);
  previous?.value.fill(0);
  const copy = new Uint8Array(value);
  privateKeyCache.set(key, { value: copy, expiresAt: Date.now() + PRIVATE_KEY_CACHE_MS });
  return new Uint8Array(copy);
}

function getCachedPrivateKey(key: string): Uint8Array | null {
  const cached = privateKeyCache.get(key);
  if (!cached) return null;
  if (cached.expiresAt <= Date.now()) {
    cached.value.fill(0);
    privateKeyCache.delete(key);
    return null;
  }
  cached.expiresAt = Date.now() + PRIVATE_KEY_CACHE_MS;
  return new Uint8Array(cached.value);
}

function clearPrivateKeyCache(): void {
  for (const cached of privateKeyCache.values()) cached.value.fill(0);
  privateKeyCache.clear();
}

function isSessionOnlyValue(key: string): boolean {
  return key === TOKEN_KEY || key === AUTH_HANDLE_KEY;
}

function bytesToBase64(bytes: Uint8Array): string {
  let value = "";
  for (const byte of bytes) value += String.fromCharCode(byte);
  return btoa(value);
}

function base64ToBytes(value: string): Uint8Array {
  return Uint8Array.from(atob(value), (c) => c.charCodeAt(0));
}

function bytesToHex(bytes: Uint8Array): string {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join("");
}

export function normalizeIdentityHandle(value: string): string {
  return value.trim().replace(/^[@#]+/, "").toLowerCase();
}

export async function hashIdentityCode(value: string): Promise<string> {
  const normalized = normalizeIdentityHandle(value);
  if (/^[a-f0-9]{64}$/.test(normalized)) return normalized;
  const input = new TextEncoder().encode(`quantumshield-identity-v1:${normalized}`);
  const digest = await crypto.subtle.digest("SHA-256", input);
  return bytesToHex(new Uint8Array(digest));
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
  if (isSessionOnlyValue(key)) {
    const sessionValue = sessionStorage.getItem(key);
    if (sessionValue) return sessionValue;
  }
  const localValue = localStorage.getItem(key);
  if (localValue) {
    if (isSessionOnlyValue(key)) {
      sessionStorage.setItem(key, localValue);
      localStorage.removeItem(key);
    }
    return localValue;
  }
  const cookieValue = getCookie(cookieName);
  if (cookieValue) {
    if (isSessionOnlyValue(key)) {
      sessionStorage.setItem(key, cookieValue);
      clearCookie(cookieName);
    } else {
      localStorage.setItem(key, cookieValue);
    }
  }
  return cookieValue;
}

function setPersistentValue(key: string, cookieName: string, value: string): void {
  if (isSessionOnlyValue(key)) {
    sessionStorage.setItem(key, value);
    localStorage.removeItem(key);
    clearCookie(cookieName);
  } else {
    localStorage.setItem(key, value);
    setCookie(cookieName, value);
  }
}

function clearPersistentValue(key: string, cookieName: string): void {
  sessionStorage.removeItem(key);
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
  const handle = getPersistentValue(LAST_HANDLE_KEY, LAST_HANDLE_COOKIE);
  if (handle && /^[a-f0-9]{64}$/.test(handle)) {
    clearPersistentValue(LAST_HANDLE_KEY, LAST_HANDLE_COOKIE);
    return null;
  }
  return handle;
}

export function setLastHandle(handle: string): void {
  const normalized = normalizeIdentityHandle(handle);
  setPersistentValue(LAST_HANDLE_KEY, LAST_HANDLE_COOKIE, normalized);
  rememberAssociatedHandle(normalized);
}

export function rememberAssociatedHandle(handle: string): void {
  const normalized = normalizeIdentityHandle(handle);
  if (!normalized || /^[a-f0-9]{64}$/.test(normalized)) return;
  const handles = new Set(getAssociatedHandles());
  handles.add(normalized);
  localStorage.setItem(ASSOCIATED_HANDLES_KEY, JSON.stringify([...handles].sort((a, b) => a.length - b.length || a.localeCompare(b))));
}

export function getAssociatedHandles(): string[] {
  try {
    const parsed = JSON.parse(localStorage.getItem(ASSOCIATED_HANDLES_KEY) ?? "[]");
    if (!Array.isArray(parsed)) return [];
    return parsed
      .filter((value): value is string => typeof value === "string")
      .map(normalizeIdentityHandle)
      .filter((value) => value && !/^[a-f0-9]{64}$/.test(value));
  } catch {
    return [];
  }
}

export function getPreferredPasskeyHandle(fallback = ""): string {
  const normalizedFallback = normalizeIdentityHandle(fallback);
  const handles = [...getAssociatedHandles(), normalizedFallback].filter(Boolean);
  return handles.sort((a, b) => a.length - b.length || a.localeCompare(b))[0] ?? normalizedFallback;
}

export function rememberUnsealedHandle(codeId: string, handle: string): void {
  const normalized = normalizeIdentityHandle(handle);
  if (!codeId || !normalized || /^[a-f0-9]{64}$/.test(normalized)) return;
  const labels = getUnsealedHandleLabels();
  labels[codeId] = normalized;
  localStorage.setItem(UNSEALED_HANDLE_LABELS_KEY, JSON.stringify(labels));
  rememberAssociatedHandle(normalized);
}

export function getUnsealedHandleLabels(): Record<string, string> {
  try {
    const parsed = JSON.parse(localStorage.getItem(UNSEALED_HANDLE_LABELS_KEY) ?? "{}");
    if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) return {};
    return Object.fromEntries(
      Object.entries(parsed)
        .filter((entry): entry is [string, string] => typeof entry[0] === "string" && typeof entry[1] === "string")
        .map(([id, handle]) => [id, normalizeIdentityHandle(handle)])
        .filter(([, handle]) => handle && !/^[a-f0-9]{64}$/.test(handle))
    );
  } catch {
    return {};
  }
}

export function getUnsealedHandle(codeId: string): string | null {
  return getUnsealedHandleLabels()[codeId] ?? null;
}

export function getDevicePasscode(): string | null {
  return localStorage.getItem(DEVICE_PASSCODE_KEY);
}

export function setDevicePasscode(passcode: string): void {
  localStorage.setItem(DEVICE_PASSCODE_KEY, passcode);
}

export function markFreshLoginVerified(durationMs = 15000): void {
  sessionStorage.setItem(FRESH_LOGIN_VERIFIED_UNTIL_KEY, String(Date.now() + durationMs));
}

export function isFreshLoginVerificationValid(): boolean {
  const until = Number(sessionStorage.getItem(FRESH_LOGIN_VERIFIED_UNTIL_KEY) ?? "0");
  if (until > Date.now()) return true;
  sessionStorage.removeItem(FRESH_LOGIN_VERIFIED_UNTIL_KEY);
  return false;
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

  const credential = await runWebAuthnCeremony(() => navigator.credentials.create({
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
  }));

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

  await runWebAuthnCeremony(() => navigator.credentials.get({
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
  }));
}

export function clearToken(): void {
  clearPersistentValue(TOKEN_KEY, TOKEN_COOKIE);
}

export function clearEphemeralSecrets(): void {
  clearPrivateKeyCache();
  localStorage.removeItem(KEM_SK_KEY);
  localStorage.removeItem(DSA_SK_KEY);
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
  const previous = getLocalKeyPair();
  void preserveKeyPairForHistory(previous);
  localStorage.setItem(KEM_PK_KEY, bytesToBase64(kemPk));
  localStorage.setItem(DSA_PK_KEY, bytesToBase64(dsaPk));
  localStorage.removeItem(KEM_SK_KEY);
  localStorage.removeItem(DSA_SK_KEY);
  cachePrivateKey(KEM_SK_KEY, kemSk);
  cachePrivateKey(DSA_SK_KEY, dsaSk);
  void storeKeyPairInIndexedDb({
    [KEM_SK_KEY]: bytesToBase64(kemSk),
    [KEM_PK_KEY]: bytesToBase64(kemPk),
    [DSA_SK_KEY]: bytesToBase64(dsaSk),
    [DSA_PK_KEY]: bytesToBase64(dsaPk),
  });
}

async function preserveKeyPairForHistory(current: {
  kemSecretKey: Uint8Array | null;
  kemPublicKey: Uint8Array | null;
  dsaSecretKey: Uint8Array | null;
  dsaPublicKey: Uint8Array | null;
}): Promise<void> {
  try {
    if (!current.kemSecretKey || !current.kemPublicKey || !current.dsaSecretKey || !current.dsaPublicKey) return;
    const entry: HistoricalKeyPair = {
      kemSecretKey: bytesToBase64(current.kemSecretKey),
      kemPublicKey: bytesToBase64(current.kemPublicKey),
      dsaSecretKey: bytesToBase64(current.dsaSecretKey),
      dsaPublicKey: bytesToBase64(current.dsaPublicKey),
      storedAt: new Date().toISOString(),
    };
    const history = await readHistoricalKeyPairs();
    if (!history.some((item) => item.kemPublicKey === entry.kemPublicKey && item.dsaPublicKey === entry.dsaPublicKey)) {
      history.push(entry);
      await storeValueInIndexedDb(HISTORICAL_KEYRING_KEY, JSON.stringify(history.slice(-8)));
    }
  } finally {
    current.kemSecretKey?.fill(0);
    current.dsaSecretKey?.fill(0);
  }
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

export async function getKemSecretKeysAsync(): Promise<Uint8Array[]> {
  const keys: Uint8Array[] = [];
  const current = await getKemSecretKeyAsync();
  if (current) keys.push(current);
  for (const historical of await readHistoricalKeyPairs()) {
    try {
      const key = base64ToBytes(historical.kemSecretKey);
      if (!keys.some((existing) => bytesToBase64(existing) === historical.kemSecretKey)) keys.push(key);
      else key.fill(0);
    } catch {
      // Skip malformed historical key records.
    }
  }
  return keys;
}

export function getDsaSecretKey(): Uint8Array | null {
  return getStoredBytes(DSA_SK_KEY);
}

function getStoredBytes(key: string): Uint8Array | null {
  if (isPrivateKey(key)) {
    const cached = getCachedPrivateKey(key);
    if (cached) return cached;
  }
  const v = localStorage.getItem(key);
  if (!v) return null;
  const bytes = base64ToBytes(v);
  if (!isPrivateKey(key)) return bytes;
  localStorage.removeItem(key);
  return cachePrivateKey(key, bytes);
}

async function getStoredBytesAsync(key: string): Promise<Uint8Array | null> {
  const existing = getStoredBytes(key);
  if (existing) return existing;
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

async function storeValueInIndexedDb(key: string, value: string): Promise<void> {
  const db = await openKeyDb();
  if (!db) return;
  await new Promise<void>((resolve) => {
    const tx = db.transaction(KEY_DB_STORE, "readwrite");
    tx.objectStore(KEY_DB_STORE).put(value, key);
    tx.oncomplete = () => resolve();
    tx.onerror = () => resolve();
    tx.onabort = () => resolve();
  });
  db.close();
}

async function getValueFromIndexedDb(key: string): Promise<string | null> {
  const db = await openKeyDb();
  if (!db) return null;
  const value = await new Promise<string | null>((resolve) => {
    const tx = db.transaction(KEY_DB_STORE, "readonly");
    const req = tx.objectStore(KEY_DB_STORE).get(key);
    req.onsuccess = () => resolve(typeof req.result === "string" ? req.result : null);
    req.onerror = () => resolve(null);
    tx.onerror = () => resolve(null);
    tx.onabort = () => resolve(null);
  });
  db.close();
  return value;
}

async function readHistoricalKeyPairs(): Promise<HistoricalKeyPair[]> {
  try {
    const raw = await getValueFromIndexedDb(HISTORICAL_KEYRING_KEY);
    const parsed = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(parsed)) return [];
    return parsed.filter((item): item is HistoricalKeyPair => (
      !!item &&
      typeof item.kemSecretKey === "string" &&
      typeof item.kemPublicKey === "string" &&
      typeof item.dsaSecretKey === "string" &&
      typeof item.dsaPublicKey === "string" &&
      typeof item.storedAt === "string"
    ));
  } catch {
    return [];
  }
}

async function deletePrivateKeysFromIndexedDb(): Promise<void> {
  const db = await openKeyDb();
  if (!db) return;
  await new Promise<void>((resolve) => {
    const tx = db.transaction(KEY_DB_STORE, "readwrite");
    tx.objectStore(KEY_DB_STORE).delete(KEM_SK_KEY);
    tx.objectStore(KEY_DB_STORE).delete(DSA_SK_KEY);
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
    if (isPrivateKey(key) && values[key]) {
      localStorage.removeItem(key);
      cachePrivateKey(key, base64ToBytes(values[key]));
      hydrated = true;
    } else if (!localStorage.getItem(key) && values[key]) {
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
  clearPrivateKeyCache();
  if (typeof indexedDB !== "undefined") indexedDB.deleteDatabase(KEY_DB_NAME);
}

export async function linkDeviceWithInvite(code: string, passcode: string): Promise<{ token: string; authHandle: string }> {
  const res = await fetch("/api/auth/link-device", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({
      code,
      passcode,
      deviceLabel: "Web device",
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

function responseErrorMessage(data: { error?: string } | null, fallback: string): string {
  if (typeof data?.error === "string" && data.error.trim()) return data.error;
  return fallback;
}

async function authedJsonFetch<T>(url: string, body: unknown, token = getToken()): Promise<T> {
  if (!token) throw new Error("You must be logged in to link a local passkey.");
  const res = await fetch(url, {
    method: "POST",
    headers: {
      "authorization": `Bearer ${token}`,
      "content-type": "application/json",
    },
    body: JSON.stringify(body),
  });
  const data = await res.json().catch(() => null) as T & { error?: string } | null;
  if (!res.ok) {
    throw new Error(responseErrorMessage(data, `${res.status} ${res.statusText || "Request failed"}`));
  }
  return data as T;
}

function devicePasskeyLabel(): string {
  const handle = getPreferredPasskeyHandle();
  if (handle) return handle;
  const device = /iphone|ipad|ipod/i.test(navigator.userAgent)
    ? "iPhone"
    : /android/i.test(navigator.userAgent)
      ? "Android"
      : /mac/i.test(navigator.userAgent)
        ? "Mac"
        : /win/i.test(navigator.userAgent)
          ? "Windows"
          : "Device";
  return `Passkey from ${device} ${new Date().toLocaleDateString(undefined, { month: "short", day: "numeric", year: "numeric" })}`;
}

function withLocalPasskeyDisplayName<T extends { user: { name: string; displayName: string } }>(optionsJSON: T, displayName: string): T {
  return {
    ...optionsJSON,
    user: {
      ...optionsJSON.user,
      name: displayName,
      displayName,
    },
  };
}

let webAuthnInFlight = false;

async function runWebAuthnCeremony<T>(fn: () => Promise<T>): Promise<T> {
  if (webAuthnInFlight) {
    throw new Error("A passkey prompt is already open. Complete or cancel it before trying again.");
  }
  webAuthnInFlight = true;
  try {
    return await fn();
  } catch (err) {
    const message = err instanceof Error ? err.message : "";
    if (/abort signal|aborted|operation was aborted/i.test(message)) {
      throw new Error("The passkey prompt was interrupted. Try again after the page finishes loading.");
    }
    throw err;
  } finally {
    webAuthnInFlight = false;
  }
}

export async function registerWithPasskey(input: {
  handle: string;
  kemPublicKey: string;
  dsaPublicKey: string;
  leadEmail?: string;
}): Promise<{ token: string; authHandle: string }> {
  const handleHash = await hashIdentityCode(input.handle);
  const optionsJSON = await jsonFetch<Parameters<typeof startRegistration>[0]["optionsJSON"]>("/api/auth/passkey/register/options", {
    handle: handleHash,
  });
  const response = await runWebAuthnCeremony(() => startRegistration({ optionsJSON: withLocalPasskeyDisplayName(optionsJSON, devicePasskeyLabel()) }));
  return jsonFetch<{ token: string; authHandle: string }>("/api/auth/passkey/register/verify", {
    handle: handleHash,
    response,
    kemPublicKey: input.kemPublicKey,
    dsaPublicKey: input.dsaPublicKey,
    leadEmail: input.leadEmail,
  });
}

export async function loginWithPasskey(handle: string): Promise<{ token: string; authHandle: string }> {
  const handleHash = await hashIdentityCode(handle);
  const optionsJSON = await jsonFetch<Parameters<typeof startAuthentication>[0]["optionsJSON"]>("/api/auth/passkey/login/options", { handle: handleHash });
  const response = await runWebAuthnCeremony(() => startAuthentication({ optionsJSON }));
  return jsonFetch<{ token: string; authHandle: string }>("/api/auth/passkey/login/verify", {
    handle: handleHash,
    response,
  });
}

function localPlatformPasskeyKey(handle: string): string {
  return `qs_platform_passkey_linked:${window.location.hostname}:${normalizeIdentityHandle(handle)}`;
}

export function clearLocalPlatformPasskeyLink(handle: string): void {
  if (typeof window === "undefined") return;
  localStorage.removeItem(localPlatformPasskeyKey(handle));
}

export async function localPlatformPasskeyAvailable(): Promise<boolean> {
  return platformAuthenticatorIsAvailable().catch(() => false);
}

export async function linkLocalPlatformPasskey(token: string, label = "Desktop passkey", handle = ""): Promise<void> {
  const optionsJSON = await authedJsonFetch<Parameters<typeof startRegistration>[0]["optionsJSON"]>("/api/auth/passkey/add/options", {}, token);
  const passkeyLabel = label || devicePasskeyLabel();
  const response = await runWebAuthnCeremony(() => startRegistration({ optionsJSON: withLocalPasskeyDisplayName(optionsJSON, passkeyLabel) }));
  await authedJsonFetch<{ ok: boolean }>("/api/auth/passkey/add/verify", { response, label: passkeyLabel }, token);
}

export async function maybeLinkLocalPlatformPasskey(handle: string, token: string, options: { force?: boolean } = {}): Promise<"linked" | "already-linked" | "skipped-mobile" | "skipped-unavailable"> {
  if (typeof window === "undefined") return "skipped-unavailable";
  if (window.matchMedia("(max-width: 767px)").matches) return "skipped-mobile";
  const storageKey = localPlatformPasskeyKey(handle);
  if (!options.force && localStorage.getItem(storageKey) === "1") return "already-linked";
  if (!(await localPlatformPasskeyAvailable())) return "skipped-unavailable";

  await new Promise((resolve) => window.setTimeout(resolve, 600));
  try {
    await linkLocalPlatformPasskey(token, devicePasskeyLabel(), handle);
    localStorage.setItem(storageKey, "1");
    return "linked";
  } catch (err) {
    const message = err instanceof Error ? err.message : "";
    if (/already linked|previously registered|already registered|excluded/i.test(message)) {
      localStorage.setItem(storageKey, "1");
      return "already-linked";
    }
    throw err;
  }
}

import { platformAuthenticatorIsAvailable, startAuthentication, startRegistration } from "@simplewebauthn/browser";
