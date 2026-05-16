import React from "react";
import { createRoot } from "react-dom/client";
import App from "./App";
import "./index.css";
import { setAuthTokenGetter } from "@workspace/api-client-react";
import { getToken } from "./lib/auth";

setAuthTokenGetter(() => getToken());

if ("serviceWorker" in navigator) {
  window.addEventListener("load", () => {
    navigator.serviceWorker.register("/sw.js", { scope: "/" }).catch((err) => {
      console.warn("Service worker registration failed", err);
    });
  });
}

createRoot(document.getElementById("root")!).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>
);
