import React from "react";
import { createRoot } from "react-dom/client";
import App from "./App";
import "./index.css";
import { setAuthTokenGetter } from "@workspace/api-client-react";
import { getToken } from "./lib/auth";

setAuthTokenGetter(() => getToken());

async function cleanupDevelopmentServiceWorkers() {
  const hadController = navigator.serviceWorker.controller !== null;
  const registrations = await navigator.serviceWorker.getRegistrations();
  await Promise.all(registrations.map((registration) => registration.unregister()));

  if ("caches" in window) {
    const names = await caches.keys();
    await Promise.all(
      names
        .filter((name) => name.startsWith("quantumshield-"))
        .map((name) => caches.delete(name)),
    );
  }

  if (hadController && sessionStorage.getItem("qs-dev-sw-cleaned") !== "true") {
    sessionStorage.setItem("qs-dev-sw-cleaned", "true");
    window.location.reload();
  }
}

async function registerProductionServiceWorker() {
  const registration = await navigator.serviceWorker.register("/sw.js", { scope: "/" });
  let refreshing = false;

  navigator.serviceWorker.addEventListener("controllerchange", () => {
    if (refreshing) return;
    refreshing = true;
    window.location.reload();
  });

  const activateWaitingWorker = () => {
    registration.waiting?.postMessage({ type: "SKIP_WAITING" });
  };

  activateWaitingWorker();

  registration.addEventListener("updatefound", () => {
    const installing = registration.installing;
    if (!installing) return;
    installing.addEventListener("statechange", () => {
      if (installing.state === "installed" && navigator.serviceWorker.controller) {
        activateWaitingWorker();
      }
    });
  });

  const checkForUpdate = () => {
    registration.update().catch((err) => {
      console.warn("Service worker update check failed", err);
    });
  };

  if (document.visibilityState === "visible") {
    checkForUpdate();
  }

  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "visible") checkForUpdate();
  });

  window.setInterval(checkForUpdate, 60 * 60 * 1000);
}

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    if (import.meta.env.DEV) {
      cleanupDevelopmentServiceWorkers()
        .catch((err) => {
          console.warn("Service worker cleanup failed", err);
        });
      return;
    }

    registerProductionServiceWorker()
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
