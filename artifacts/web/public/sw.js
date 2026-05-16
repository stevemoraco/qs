/* QuantumShield Service Worker */
const CACHE_NAME = "quantumshield-v1";

self.addEventListener("install", (event) => {
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  event.waitUntil(self.clients.claim());
});

self.addEventListener("fetch", (event) => {
  // Network-first; let the app handle its own caching strategy
  return;
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
    icon: "/favicon.svg",
    badge: "/favicon.svg",
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
