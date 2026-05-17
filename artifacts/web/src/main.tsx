import React from "react";
import { createRoot } from "react-dom/client";
import App from "./App";
import "./index.css";
import { setAuthTokenGetter } from "@workspace/api-client-react";
import { getToken } from "./lib/auth";

setAuthTokenGetter(() => getToken());

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    if (import.meta.env.DEV) {
      navigator.serviceWorker.getRegistrations()
        .then((registrations) => Promise.all(registrations.map((registration) => registration.unregister())))
        .then(() => {
          if (!("caches" in window)) return undefined;
          return caches.keys().then((names) => Promise.all(
            names
              .filter((name) => name.startsWith("quantumshield-"))
              .map((name) => caches.delete(name)),
          ));
        })
        .catch((err) => {
          console.warn("Service worker cleanup failed", err);
        });
      return;
    }

    navigator.serviceWorker.register("/sw.js", { scope: "/" })
      .catch((err) => {
        console.warn("Service worker registration failed", err);
      });
  });
}

createRoot(document.getElementById("root")!).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>
);
