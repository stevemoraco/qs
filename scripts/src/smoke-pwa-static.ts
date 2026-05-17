import { access, readFile, stat } from "node:fs/promises";
import path from "node:path";

const root = path.resolve(import.meta.dirname, "..", "..");
const publicDir = path.join(root, "artifacts/web/public");
const distDir = path.join(root, "artifacts/web/dist/public");

type Check = {
  name: string;
  pass: boolean;
  detail?: string;
};

async function exists(filePath: string): Promise<boolean> {
  try {
    await access(filePath);
    return true;
  } catch {
    return false;
  }
}

async function fileSize(filePath: string): Promise<number> {
  try {
    return (await stat(filePath)).size;
  } catch {
    return 0;
  }
}

const manifestText = await readFile(path.join(publicDir, "manifest.webmanifest"), "utf8");
const manifest = JSON.parse(manifestText) as {
  name?: unknown;
  short_name?: unknown;
  start_url?: unknown;
  scope?: unknown;
  display?: unknown;
  icons?: Array<{ src?: string; sizes?: string; type?: string; purpose?: string }>;
};
const sw = await readFile(path.join(publicDir, "sw.js"), "utf8");

const iconChecks = await Promise.all(
  (manifest.icons ?? []).map(async (icon) => {
    const src = typeof icon.src === "string" ? icon.src.replace(/^\//, "") : "";
    return {
      icon,
      exists: !!src && await exists(path.join(publicDir, src)),
      size: src ? await fileSize(path.join(publicDir, src)) : 0,
    };
  }),
);

const distChecks = await Promise.all([
  exists(path.join(distDir, "index.html")),
  exists(path.join(distDir, "manifest.webmanifest")),
  exists(path.join(distDir, "sw.js")),
  exists(path.join(distDir, "icon-192.png")),
  exists(path.join(distDir, "icon-512.png")),
]);

const checks: Check[] = [
  {
    name: "manifest is installable standalone PWA metadata",
    pass:
      manifest.name === "QuantumShield" &&
      manifest.short_name === "QuantumShield" &&
      manifest.start_url === "/" &&
      manifest.scope === "/" &&
      manifest.display === "standalone",
  },
  {
    name: "manifest declares 192, 512, and maskable icons that exist",
    pass:
      iconChecks.some(({ icon, exists, size }) => exists && size > 0 && icon.sizes === "192x192" && icon.purpose?.includes("maskable")) &&
      iconChecks.some(({ icon, exists, size }) => exists && size > 0 && icon.sizes === "512x512" && icon.purpose?.includes("maskable")),
  },
  {
    name: "service worker caches app shell and bypasses API GETs",
    pass:
      sw.includes("const APP_SHELL") &&
      sw.includes("\"/app\"") &&
      sw.includes("\"/manifest.webmanifest\"") &&
      sw.includes("url.pathname.startsWith(\"/api/\")") &&
      sw.includes("event.request.mode === \"navigate\""),
  },
  {
    name: "service worker supports push notification click-through",
    pass:
      sw.includes("self.addEventListener(\"push\"") &&
      sw.includes("showNotification") &&
      sw.includes("self.addEventListener(\"notificationclick\"") &&
      sw.includes("openWindow"),
  },
  {
    name: "production build emitted install/static assets",
    pass: distChecks.every(Boolean),
    detail: "run `pnpm --filter @workspace/web run build` before this smoke check",
  },
];

let failed = 0;
for (const check of checks) {
  if (!check.pass) failed += 1;
  console.log(`${check.pass ? "ok" : "not ok"} - ${check.name}${check.detail ? ` (${check.detail})` : ""}`);
}
if (failed > 0) process.exitCode = 1;
