let deferredInstallPrompt: BeforeInstallPromptEvent | null = null;
const installListeners = new Set<() => void>();

interface BeforeInstallPromptEvent extends Event {
  prompt: () => Promise<void>;
  userChoice: Promise<{ outcome: "accepted" | "dismissed" }>;
}

if (typeof window !== "undefined") {
  window.addEventListener("beforeinstallprompt", (e) => {
    e.preventDefault();
    deferredInstallPrompt = e as BeforeInstallPromptEvent;
    installListeners.forEach((cb) => cb());
  });

  window.addEventListener("appinstalled", () => {
    deferredInstallPrompt = null;
    installListeners.forEach((cb) => cb());
  });
}

export function isStandalone(): boolean {
  if (typeof window === "undefined") return false;
  return (
    window.matchMedia("(display-mode: standalone)").matches ||
    window.matchMedia("(display-mode: fullscreen)").matches ||
    // iOS Safari
    (window.navigator as { standalone?: boolean }).standalone === true
  );
}

export function canPromptInstall(): boolean {
  return deferredInstallPrompt !== null;
}

export async function promptInstall(): Promise<"accepted" | "dismissed" | "unavailable"> {
  if (!deferredInstallPrompt) return "unavailable";
  try {
    await deferredInstallPrompt.prompt();
    const { outcome } = await deferredInstallPrompt.userChoice;
    deferredInstallPrompt = null;
    installListeners.forEach((cb) => cb());
    return outcome;
  } catch {
    return "dismissed";
  }
}

export function onInstallStateChange(cb: () => void): () => void {
  installListeners.add(cb);
  return () => installListeners.delete(cb);
}

export function notificationPermission(): NotificationPermission | "unsupported" {
  if (typeof Notification === "undefined") return "unsupported";
  return Notification.permission;
}

export async function requestNotificationPermission(): Promise<NotificationPermission | "unsupported"> {
  if (typeof Notification === "undefined") return "unsupported";
  return await Notification.requestPermission();
}

function urlBase64ToUint8Array(base64String: string): Uint8Array {
  const value = base64String.trim().replace(/^["']|["']$/g, "");
  const padding = "=".repeat((4 - (value.length % 4)) % 4);
  const base64 = (value + padding).replace(/-/g, "+").replace(/_/g, "/");
  const raw = atob(base64);
  const out = new Uint8Array(raw.length);
  for (let i = 0; i < raw.length; i++) out[i] = raw.charCodeAt(i);
  return out;
}

function isLikelyP256PublicKey(bytes: Uint8Array): boolean {
  return bytes.byteLength === 65 && bytes[0] === 0x04;
}

function arrayBufferEquals(a: ArrayBuffer | null, b: Uint8Array): boolean {
  if (!a) return false;
  const left = new Uint8Array(a);
  if (left.byteLength !== b.byteLength) return false;
  for (let i = 0; i < left.byteLength; i++) {
    if (left[i] !== b[i]) return false;
  }
  return true;
}

export async function registerServiceWorker(): Promise<ServiceWorkerRegistration | null> {
  if (!("serviceWorker" in navigator)) return null;
  try {
    return await navigator.serviceWorker.register("/sw.js", { scope: "/" });
  } catch (e) {
    console.error("SW registration failed", e);
    return null;
  }
}

async function readyServiceWorker(): Promise<ServiceWorkerRegistration | null> {
  const registered = await registerServiceWorker();
  if (!registered) return null;
  return await Promise.race<ServiceWorkerRegistration | null>([
    navigator.serviceWorker.ready,
    new Promise((resolve) => setTimeout(() => resolve(registered), 2500)),
  ]);
}

export type PushSubscriptionResult =
  | { ok: true; reason: "subscribed" }
  | { ok: false; reason: string };

async function fetchVapidPublicKey(): Promise<PushSubscriptionResult & { publicKey?: string }> {
  let res: Response;
  try {
    res = await fetch("/api/push/vapid-public-key", {
      cache: "no-store",
      headers: { accept: "application/json" },
    });
  } catch (err) {
    return { ok: false, reason: err instanceof Error ? `Could not reach push key endpoint: ${err.message}` : "Could not reach push key endpoint." };
  }

  const text = await res.text().catch(() => "");
  let data: { publicKey?: unknown; error?: unknown } | null = null;
  try {
    data = text ? JSON.parse(text) : null;
  } catch {
    // Non-JSON response, include a short preview below.
  }

  if (!res.ok) {
    const message = typeof data?.error === "string" ? data.error : text.slice(0, 120) || res.statusText;
    return { ok: false, reason: `Push key endpoint returned ${res.status}: ${message}` };
  }

  if (typeof data?.publicKey !== "string" || data.publicKey.trim().length === 0) {
    return { ok: false, reason: `Push key endpoint returned invalid JSON: ${text.slice(0, 120) || "empty response"}` };
  }

  return { ok: true, reason: "subscribed", publicKey: data.publicKey };
}

export async function ensurePushSubscription(authToken: string): Promise<PushSubscriptionResult> {
  if (!("serviceWorker" in navigator)) return { ok: false, reason: "Service workers are not supported in this browser." };
  if (!("PushManager" in window)) return { ok: false, reason: "Push notifications are not supported in this browser." };
  try {
    const reg = await readyServiceWorker();
    if (!reg) return { ok: false, reason: "Service worker registration is not ready." };

    const vapidKeyResult = await fetchVapidPublicKey();
    if (!vapidKeyResult.ok) return vapidKeyResult;
    const vapidKey = vapidKeyResult.publicKey;
    if (!vapidKey) return { ok: false, reason: "Push key endpoint did not include a public key." };

    const permission = notificationPermission() === "granted" ? "granted" : await requestNotificationPermission();
    if (permission !== "granted") return { ok: false, reason: permission === "denied" ? "Notifications are blocked for this site." : "Notification permission was not granted." };

    const keyBytes = urlBase64ToUint8Array(vapidKey);
    if (!isLikelyP256PublicKey(keyBytes)) {
      return { ok: false, reason: "Server push key is invalid. VAPID_PUBLIC_KEY must be a P-256 public key." };
    }
    let sub = await reg.pushManager.getSubscription();
    if (sub && !arrayBufferEquals(sub.options.applicationServerKey, keyBytes)) {
      await sub.unsubscribe();
      sub = null;
    }
    if (!sub) {
      sub = await reg.pushManager.subscribe({
        userVisibleOnly: true,
        applicationServerKey: keyBytes.buffer.slice(
          keyBytes.byteOffset,
          keyBytes.byteOffset + keyBytes.byteLength,
        ) as ArrayBuffer,
      });
    }

    const json = sub.toJSON();
    const res = await fetch("/api/push/subscribe", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Authorization: `Bearer ${authToken}`,
      },
      body: JSON.stringify({
        endpoint: json.endpoint,
        keys: json.keys,
        userAgent: navigator.userAgent,
      }),
    });
    if (!res.ok) {
      const data = await res.json().catch(() => null) as { error?: string } | null;
      return { ok: false, reason: data?.error ?? "Server rejected the push subscription." };
    }
    return { ok: true, reason: "subscribed" };
  } catch (e) {
    console.error("Push subscription failed", e);
    return { ok: false, reason: e instanceof Error ? e.message : "Push subscription failed." };
  }
}

export async function subscribeToPush(authToken: string): Promise<boolean> {
  return (await ensurePushSubscription(authToken)).ok;
}
