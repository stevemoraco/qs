/* QuantumShield Service Worker */
const CACHE_NAME = "quantumshield-v4";
const MODEL_CACHE_NAME = "quantumshield-models-v1";
const MODEL_HOSTS = ["huggingface.co", "storage.googleapis.com", "tfhub.dev"];
const MODEL_HOST_SUFFIXES = [".huggingface.co", ".hf.co", ".xethub.hf.co"];
const APP_SHELL = [
  "/",
  "/app",
  "/index.html",
  "/manifest.webmanifest",
  "/favicon.png",
  "/icon-192.png",
  "/icon-512.png",
  "/apple-touch-icon.png",
];

function isModelHost(hostname) {
  return MODEL_HOSTS.includes(hostname) || MODEL_HOST_SUFFIXES.some((suffix) => hostname.endsWith(suffix));
}

self.addEventListener("install", (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME).then((cache) => cache.addAll(APP_SHELL).catch(() => undefined)),
  );
});

self.addEventListener("activate", (event) => {
  event.waitUntil(
    caches.keys().then((names) => Promise.all(
      names
        .filter((name) => name !== CACHE_NAME && name !== MODEL_CACHE_NAME)
        .map((name) => caches.delete(name)),
    )),
  );
});

self.addEventListener("fetch", (event) => {
  const url = new URL(event.request.url);
  if (event.request.method !== "GET") return;

  if (url.origin === self.location.origin && url.pathname.startsWith("/api/")) return;

  if (event.request.mode === "navigate") {
    event.respondWith(
      fetch(event.request)
        .then((response) => {
          if (response.ok) {
            const copy = response.clone();
            caches.open(CACHE_NAME).then((cache) => {
              cache.put("/", copy.clone());
              cache.put("/app", copy);
            });
          }
          return response;
        })
        .catch(async () => (await caches.match("/app")) || (await caches.match("/index.html")) || Response.error()),
    );
    return;
  }

  const isModelRequest =
    isModelHost(url.hostname) ||
    url.pathname.includes("/resolve/") ||
    url.pathname.endsWith(".onnx") ||
    url.pathname.endsWith(".wasm") ||
    (url.pathname.endsWith(".json") && url.pathname.includes("model"));

  if (!isModelRequest && url.origin !== self.location.origin) return;

  event.respondWith(
    caches.open(isModelRequest ? MODEL_CACHE_NAME : CACHE_NAME).then(async (cache) => {
      const cached = await cache.match(event.request);
      if (cached) return cached;

      const response = await fetch(event.request);
      if (response.ok) {
        cache.put(event.request, response.clone());
      }
      return response;
    }),
  );
});

self.addEventListener("push", (event) => {
  let payload = { title: "QuantumShield", body: "You have a new encrypted message." };
  try {
    if (event.data) {
      const data = event.data.json();
      payload = { ...payload, ...data };
    }
  } catch (e) {
    if (event.data) {
      payload.body = event.data.text();
    }
  }

  const options = {
    body: payload.body,
    icon: "/icon-192.png",
    badge: "/icon-192.png",
    vibrate: [80, 40, 80],
    data: payload.url || "/app",
    tag: payload.tag || "quantumshield-msg",
  };

  event.waitUntil(self.registration.showNotification(payload.title, options));
});

self.addEventListener("notificationclick", (event) => {
  event.notification.close();
  const url = event.notification.data || "/app";
  event.waitUntil(
    self.clients.matchAll({ type: "window", includeUncontrolled: true }).then((clientList) => {
      for (const client of clientList) {
        if (client.url.includes(url) && "focus" in client) return client.focus();
      }
      if (self.clients.openWindow) return self.clients.openWindow(url);
    }),
  );
});
