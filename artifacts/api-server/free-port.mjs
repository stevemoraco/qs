import { readFileSync, readdirSync, readlinkSync } from "node:fs";
import { setTimeout as sleep } from "node:timers/promises";
import { fileURLToPath } from "node:url";
import { dirname, resolve, sep } from "node:path";

const port = Number(process.env.PORT || 8080);
const portHex = port.toString(16).toUpperCase().padStart(4, "0");
const selfPid = String(process.pid);
const apiServerDir = resolve(dirname(fileURLToPath(import.meta.url)));
const cmdlineMarkers = [
  "@workspace/api-server",
  "artifacts/api-server",
  "replit-run-latest.sh",
  "run replit:latest",
];

function inodesListeningOn(file) {
  let text;
  try { text = readFileSync(file, "utf8"); } catch { return new Set(); }
  const inodes = new Set();
  for (const line of text.split("\n").slice(1)) {
    const parts = line.trim().split(/\s+/);
    if (parts.length < 10) continue;
    const localAddr = parts[1];
    const state = parts[3];
    const inode = parts[9];
    if (state !== "0A") continue;
    if (!localAddr || !localAddr.endsWith(":" + portHex)) continue;
    if (inode && inode !== "0") inodes.add(inode);
  }
  return inodes;
}

function readCmdline(pid) {
  try {
    return readFileSync(`/proc/${pid}/cmdline`, "utf8").replace(/\0/g, " ").trim();
  } catch { return ""; }
}

function readCwd(pid) {
  try { return readlinkSync(`/proc/${pid}/cwd`); } catch { return ""; }
}

function readPpid(pid) {
  try {
    const text = readFileSync(`/proc/${pid}/status`, "utf8");
    const m = /^PPid:\s*(\d+)/m.exec(text);
    return m ? m[1] : "";
  } catch { return ""; }
}

function cmdlineMatches(text) {
  if (!text) return false;
  return cmdlineMarkers.some((marker) => text.includes(marker));
}

function cwdMatches(cwd) {
  if (!cwd) return false;
  const normalized = resolve(cwd);
  return normalized === apiServerDir || normalized.startsWith(apiServerDir + sep);
}

function isApiServerProcess(pid) {
  const seen = new Set();
  let cursor = pid;
  while (cursor && !seen.has(cursor) && cursor !== "1" && cursor !== "0") {
    seen.add(cursor);
    if (cmdlineMatches(readCmdline(cursor))) return true;
    if (cwdMatches(readCwd(cursor))) return true;
    cursor = readPpid(cursor);
  }
  return false;
}

const targetInodes = new Set([
  ...inodesListeningOn("/proc/net/tcp"),
  ...inodesListeningOn("/proc/net/tcp6"),
]);
if (targetInodes.size === 0) process.exit(0);

const pidsOwningPort = new Set();
for (const pid of readdirSync("/proc")) {
  if (!/^\d+$/.test(pid)) continue;
  if (pid === selfPid) continue;
  let fds;
  try { fds = readdirSync(`/proc/${pid}/fd`); } catch { continue; }
  for (const fd of fds) {
    let link;
    try { link = readlinkSync(`/proc/${pid}/fd/${fd}`); } catch { continue; }
    const m = /^socket:\[(\d+)\]$/.exec(link);
    if (m && targetInodes.has(m[1])) { pidsOwningPort.add(pid); break; }
  }
}

const stalePids = [...pidsOwningPort].filter((pid) => isApiServerProcess(pid));

const skipped = [...pidsOwningPort].filter((pid) => !stalePids.includes(pid));
if (skipped.length) {
  console.warn(`free-port: leaving non-api-server processes on port ${port}: ${skipped.join(", ")}`);
}
if (stalePids.length === 0) process.exit(0);

console.log(`free-port: terminating stale api-server processes on port ${port}: ${stalePids.join(", ")}`);
for (const pid of stalePids) {
  try { process.kill(Number(pid), "SIGTERM"); } catch {}
}
await sleep(800);
for (const pid of stalePids) {
  try { process.kill(Number(pid), 0); } catch { continue; }
  try { process.kill(Number(pid), "SIGKILL"); } catch {}
}
