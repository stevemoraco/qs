import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";

export const PACKAGE_VERSION = "2026.5.16-1108mdt";
export const SERVER_STARTED_AT = new Date().toISOString();

export function versionLabelFromIso(value: string): string {
  const date = new Date(value);
  const source = Number.isNaN(date.getTime()) ? new Date() : date;
  const parts = new Intl.DateTimeFormat("en-US", {
    timeZone: "America/Denver",
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
    hour: "2-digit",
    minute: "2-digit",
    hour12: true,
    timeZoneName: "short",
  }).formatToParts(source);
  const part = (type: string) => parts.find((item) => item.type === type)?.value ?? "";
  return `v${part("year")}.${part("month")}.${part("day")}.${part("hour")}.${part("minute")}${part("dayPeriod").toUpperCase()}.${part("timeZoneName")}`;
}

function git(args: string[]): string {
  return execFileSync("git", args, {
    cwd: process.cwd(),
    encoding: "utf8",
    stdio: ["ignore", "pipe", "ignore"],
  }).trim();
}

function safeGit(args: string[], fallback = "unavailable"): string {
  try {
    return git(args);
  } catch {
    return fallback;
  }
}

function md5(input: string): string {
  return createHash("md5").update(input).digest("hex");
}

function sha256(input: string): string {
  return createHash("sha256").update(input).digest("hex");
}

function repoRoot(): string {
  return safeGit(["rev-parse", "--show-toplevel"], process.cwd());
}

function trackedRepoDigest(root: string, algorithm: "md5" | "sha256"): string {
  try {
    const files = git(["ls-files", "-z"]).split("\0").filter(Boolean).sort();
    const hash = createHash(algorithm);
    for (const file of files) {
      const path = `${root}/${file}`;
      if (!existsSync(path)) continue;
      hash.update(file);
      hash.update("\0");
      hash.update(readFileSync(path));
      hash.update("\0");
    }
    return hash.digest("hex");
  } catch {
    return "unavailable";
  }
}

export function gitSnapshot() {
  const root = repoRoot();
  const commit = safeGit(["rev-parse", "HEAD"]);
  const originMainCommit = safeGit(["rev-parse", "origin/main"]);
  const status = safeGit(["status", "--porcelain"], "");
  return {
    root,
    branch: safeGit(["rev-parse", "--abbrev-ref", "HEAD"]),
    commit,
    shortCommit: safeGit(["rev-parse", "--short", "HEAD"]),
    commitSubject: safeGit(["log", "-1", "--format=%s"]),
    committedAtUtc: safeGit(["log", "-1", "--format=%cI"]),
    displayVersion: versionLabelFromIso(safeGit(["log", "-1", "--format=%cI"])),
    originMainCommit,
    originMainShortCommit: originMainCommit === "unavailable" ? "unavailable" : originMainCommit.slice(0, 7),
    originMainCommittedAtUtc: originMainCommit === "unavailable" ? "unavailable" : safeGit(["log", "-1", "--format=%cI", originMainCommit]),
    originMainDisplayVersion: originMainCommit === "unavailable" ? "unavailable" : versionLabelFromIso(safeGit(["log", "-1", "--format=%cI", originMainCommit])),
    dirty: status.length > 0,
    dirtySummary: status ? status.split("\n").slice(0, 50) : [],
    commitMd5: md5(commit),
    commitSha256: sha256(commit),
    repoMd5: trackedRepoDigest(root, "md5"),
    repoSha256: trackedRepoDigest(root, "sha256"),
  };
}

export const BOOT_GIT = gitSnapshot();

export function versionAuditPayload() {
  const currentGit = gitSnapshot();
  const serverBootMatchesCurrentGit = BOOT_GIT.commit === currentGit.commit && BOOT_GIT.repoSha256 === currentGit.repoSha256;
  return {
    app: "QuantumShield",
    displayVersion: versionLabelFromIso(BOOT_GIT.committedAtUtc || SERVER_STARTED_AT),
    packageVersion: PACKAGE_VERSION,
    serverStartedAtUtc: SERVER_STARTED_AT,
    publishTimeUtc: BOOT_GIT.committedAtUtc,
    latestCodeRunning: serverBootMatchesCurrentGit && !BOOT_GIT.dirty,
    runningState: {
      serverBootMatchesCurrentGit,
      serverBootDirty: BOOT_GIT.dirty,
      currentWorkspaceDirty: currentGit.dirty,
      currentHeadMatchesOriginMain: currentGit.commit === currentGit.originMainCommit,
    },
    git: {
      boot: BOOT_GIT,
      current: currentGit,
    },
  };
}

export function errorLogVersionContext(client?: { commit?: string | null; version?: string | null }) {
  const audit = versionAuditPayload();
  return {
    clientCommit: client?.commit ?? null,
    clientVersion: client?.version ?? null,
    serverCommit: audit.git.boot.shortCommit,
    serverVersion: audit.displayVersion,
    serverStartedAt: new Date(audit.serverStartedAtUtc),
  };
}
