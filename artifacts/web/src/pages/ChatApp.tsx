import { useState, useEffect, useMemo, useRef, useCallback } from "react";
import { useLocation } from "wouter";
import {
  Shield,
  Plus,
  LogOut,
  MessageSquare,
  Users,
  Clock,
  Lock,
  Send,
  X,
  Search,
  ArrowLeft,
  Github,
  Fingerprint,
  KeyRound,
  Settings,
  CameraOff,
  AlertTriangle,
  Trash2,
} from "lucide-react";
import {
  useGetRooms,
  getGetRoomsQueryKey,
  usePostRooms,
  useGetAuthMe,
  getGetAuthMeQueryKey,
  usePostAuthLogout,
  useGetRoomsRoomIdMessages,
  getGetRoomsRoomIdMessagesQueryKey,
  postRoomsRoomIdMessages,
  useGetRoomsRoomIdMembers,
  getRoomsRoomIdMembers,
  getKeysUserId,
  useGetUsersSearch,
  getGetUsersSearchQueryKey,
  getGetRoomsRoomIdMembersQueryKey,
  getGetIdentityCodesQueryKey,
  useGetIdentityCodes,
  usePatchIdentityCodesCodeId,
  usePostIdentityCodes,
  usePostKeysUpload,
  type IdentityCode,
  type SendMessageRequest,
} from "@workspace/api-client-react";
import { useQueryClient } from "@tanstack/react-query";
import { clearEphemeralSecrets, clearToken, getDsaPublicKey, getDsaPublicKeysAsync, getKemSecretKeysAsync, getLastHandle, getLocalKeyPairAsync, getToken, getUnsealedHandleLabels, hashIdentityCode, isFreshLoginVerificationValid, linkLocalPlatformPasskey, loginWithPasskey, rememberAssociatedHandle, rememberUnsealedHandle, setAuthHandle, setLastHandle, setToken, storeKeyPair, verifyDevice } from "@/lib/auth";
import { clearBytes, decryptMessage, encryptMessage, importMessageKey, CIPHER_SUITE } from "@/lib/crypto";
import { getFrameThreatDetector } from "@/lib/on-device-vision";
import { ml_kem1024 } from "@noble/post-quantum/ml-kem.js";
import { ml_dsa87 } from "@noble/post-quantum/ml-dsa.js";
import { ensurePushSubscription, hasExistingPushSubscription, notificationPermission } from "@/lib/pwa";
import {
  cacheRoomMembers,
  cacheRoomMessages,
  cacheRooms,
  cacheTrustedKeyBundle,
  createLocalOutboxId,
  deleteOutboxEntry,
  enqueueOutbox,
  getCachedRoomMembers,
  getCachedRoomMessages,
  getCachedRooms,
  getCachedTrustedKeyBundle,
  getOutboxEntries,
  type OfflineOutboxEntry,
} from "@/lib/offline-vault";
import { useIsMobile } from "@/hooks/use-mobile";

const GITHUB_URL = "https://github.com/stevemoraco/qs";
const VERSION_LABEL_FALLBACK = "VERSION";
declare const __QS_CLIENT_COMMIT__: string;
const CLIENT_COMMIT = typeof __QS_CLIENT_COMMIT__ === "string" ? __QS_CLIENT_COMMIT__ : "unknown";
type VersionTone = "ok" | "remote-behind" | "mismatch";
const CAPTURE_WARNING_MS = 8000;
const FLASH_SCAN_MS = 60;
const FLASH_FRAME_WIDTH = 64;
const FLASH_FRAME_HEIGHT = 40;
const FLASH_DEBUG_SEND_MS = 500;
const KEY_BUNDLE_TRUST_KEY = "qs_trusted_key_bundles_v1";
const KEY_BUNDLE_WARNING_KEY = "qs_key_bundle_warning_v1";
const OFFLINE_ME_KEY = "qs_offline_me_v1";
const LEGACY_SIGNATURE_GRACE_BEFORE_MS = Date.parse("2026-05-17T09:42:00Z");

function normalizeCodeInput(value: string): string {
  return value.trim().replace(/^[@#]+/, "").toLowerCase();
}

function bytesToBase64(bytes: Uint8Array): string {
  let value = "";
  for (const byte of bytes) value += String.fromCharCode(byte);
  return btoa(value);
}

function sameBase64Bytes(a: string | null | undefined, b: Uint8Array | null): boolean {
  return !!a && !!b && a === bytesToBase64(b);
}

function base64ToBytes(value: string): Uint8Array {
  return Uint8Array.from(atob(value), (char) => char.charCodeAt(0));
}

type KeyBundle = {
  kemPublicKey?: string | null;
  dsaPublicKey?: string | null;
  kemSignature?: string | null;
};

type RecipientEncryptedKeyValue = string | string[];
type RecipientEncryptedKeys = Record<string, RecipientEncryptedKeyValue>;
type SendRecipientEncryptedKeys = SendMessageRequest["recipientEncryptedKeys"];

type OfflineMe = {
  id: string;
  username: string;
  displayName?: string | null;
  avatarColor?: string | null;
  kemPublicKey?: string | null;
  dsaPublicKey?: string | null;
};

type VersionAudit = {
  app: string;
  displayVersion: string;
  packageVersion: string;
  serverStartedAtUtc: string;
  publishTimeUtc: string;
  latestCodeRunning: boolean;
  runningState: {
    serverBootMatchesCurrentGit: boolean;
    serverBootDirty: boolean;
    currentWorkspaceDirty: boolean;
    currentHeadMatchesOriginMain: boolean;
  };
  git: {
    boot: VersionGitSnapshot;
    current: VersionGitSnapshot;
  };
  runtime: {
    node: string;
    platform: string;
    arch: string;
    pid: number;
    replit?: Record<string, string | null>;
  };
  attestations: Record<string, {
    status: string;
    reason?: string;
    bootRepoSha256?: string;
    currentRepoSha256?: string;
  }>;
};

type VersionGitSnapshot = {
  branch: string;
  commit: string;
  shortCommit: string;
  commitSubject: string;
  committedAtUtc: string;
  displayVersion: string;
  originMainCommit: string;
  originMainShortCommit: string;
  originMainCommittedAtUtc: string;
  originMainDisplayVersion: string;
  dirty: boolean;
  dirtySummary: string[];
  commitMd5: string;
  commitSha256: string;
  repoMd5: string;
  repoSha256: string;
};

function readJson<T>(key: string, fallback: T): T {
  try {
    const value = localStorage.getItem(key);
    return value ? JSON.parse(value) as T : fallback;
  } catch {
    return fallback;
  }
}

function writeJson(key: string, value: unknown): void {
  localStorage.setItem(key, JSON.stringify(value));
}

function loadOfflineMe(): OfflineMe | null {
  return readJson<OfflineMe | null>(OFFLINE_ME_KEY, null);
}

function saveOfflineMe(me: OfflineMe): void {
  writeJson(OFFLINE_ME_KEY, me);
}

function sendRecipientEncryptedKeys(keys: RecipientEncryptedKeys): SendRecipientEncryptedKeys {
  return keys as SendRecipientEncryptedKeys;
}

function errorMessage(err: unknown): string {
  return err instanceof Error ? err.message : "Unknown error";
}

function formatAuditTime(value: string, timeZone?: string): string {
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return "unavailable";
  return new Intl.DateTimeFormat(undefined, {
    timeZone,
    year: "numeric",
    month: "short",
    day: "2-digit",
    hour: "numeric",
    minute: "2-digit",
    second: "2-digit",
    timeZoneName: "short",
  }).format(date);
}

function formatBrowserAuditTime(value: number): string {
  return new Intl.DateTimeFormat(undefined, {
    year: "numeric",
    month: "short",
    day: "2-digit",
    hour: "numeric",
    minute: "2-digit",
    second: "2-digit",
    timeZoneName: "short",
  }).format(new Date(value));
}

function formatElapsedSince(value: string, nowMs: number): string {
  const then = new Date(value).getTime();
  if (!Number.isFinite(then)) return "unavailable";
  const seconds = Math.max(0, Math.floor((nowMs - then) / 1000));
  const days = Math.floor(seconds / 86400);
  const hours = Math.floor((seconds % 86400) / 3600);
  const minutes = Math.floor((seconds % 3600) / 60);
  if (days > 0) return `${days}d ${hours}h ${minutes}m`;
  if (hours > 0) return `${hours}h ${minutes}m`;
  return `${minutes}m ${seconds % 60}s`;
}

function versionLabelFromIso(value: string): string {
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

function versionLabelForSnapshot(snapshot?: VersionGitSnapshot): string {
  return snapshot?.displayVersion || versionLabelFromIso(snapshot?.committedAtUtc ?? "");
}

function shortCommit(value?: string | null): string {
  return value ? value.slice(0, 7) : "unknown";
}

function versionStatus(audit: VersionAudit | null): VersionTone {
  if (!audit) return "mismatch";
  const client = CLIENT_COMMIT;
  const server = audit.git.boot.shortCommit;
  const local = audit.git.current.shortCommit;
  const remote = shortCommit(audit.git.current.originMainCommit || audit.git.boot.originMainCommit);
  const runtimeClean = audit.runningState.serverBootMatchesCurrentGit && !audit.runningState.serverBootDirty && !audit.runningState.currentWorkspaceDirty;
  if (client !== server || server !== local || !runtimeClean) return "mismatch";
  if (remote !== local) return "remote-behind";
  return "ok";
}

function VersionBadge({ label, onClick, className = "", tone = "ok" }: { label: string; onClick: () => void; className?: string; tone?: VersionTone }) {
  const toneClass = tone === "mismatch"
    ? "text-destructive hover:text-destructive"
    : tone === "remote-behind"
      ? "text-amber-500 hover:text-amber-500"
      : "text-muted-foreground hover:text-primary";
  return (
    <button
      type="button"
      onClick={onClick}
      className={`font-mono text-[10px] leading-none transition-colors ${toneClass} ${className}`}
      data-testid="button-version-audit"
    >
      {label}
    </button>
  );
}

function VersionAuditModal({ open, onClose }: { open: boolean; onClose: () => void }) {
  const [audit, setAudit] = useState<VersionAudit | null>(null);
  const [error, setError] = useState("");
  const [nowMs, setNowMs] = useState(() => Date.now());

  useEffect(() => {
    if (!open) return;
    let cancelled = false;
    setError("");
    fetch("/api/version", { cache: "no-store" })
      .then((res) => {
        if (!res.ok) throw new Error(`${res.status} ${res.statusText || "version request failed"}`);
        return res.json() as Promise<VersionAudit>;
      })
      .then((data) => {
        if (!cancelled) setAudit(data);
      })
      .catch((err) => {
        if (!cancelled) setError(err instanceof Error ? err.message : "Could not load version audit.");
      });
    const interval = window.setInterval(() => setNowMs(Date.now()), 1000);
    return () => {
      cancelled = true;
      window.clearInterval(interval);
    };
  }, [open]);

  if (!open) return null;
  const clientAttestation = {
    userAgent: navigator.userAgent,
    platform: navigator.platform,
    language: navigator.language,
    online: navigator.onLine,
    webCrypto: !!window.crypto?.subtle,
    webAuthn: typeof PublicKeyCredential !== "undefined",
    serviceWorker: "serviceWorker" in navigator,
  };
  const boot = audit?.git.boot;
  const publishUtc = audit?.publishTimeUtc ?? "";
  const tone = versionStatus(audit);
  const current = audit?.git.current;
  const remoteCommit = shortCommit(current?.originMainCommit || boot?.originMainCommit);
  const versionBoxClass = "border border-border/50 bg-background/50 p-3 min-w-0";
  const versionValueClass = "mt-1 break-all text-sm font-bold text-foreground";
  const versionHashClass = "mt-2 break-all text-[10px] text-muted-foreground";
  const statusCopy = tone === "ok"
    ? "CLIENT, SERVER, LOCAL, AND REMOTE MATCH"
    : tone === "remote-behind"
      ? "CLIENT, SERVER, AND LOCAL MATCH. GITHUB REMOTE IS BEHIND."
      : "CLIENT, SERVER, OR LOCAL VERSION MISMATCH";

  return (
    <div className="fixed inset-0 z-[120] bg-background/80 backdrop-blur-sm flex items-center justify-center p-4" onClick={onClose}>
      <div className="w-full max-w-3xl max-h-[88vh] overflow-y-auto border border-border bg-card text-left" onClick={(event) => event.stopPropagation()}>
        <div className="flex items-start justify-between gap-4 border-b border-border/50 p-4">
          <div>
            <div className="font-mono text-[10px] tracking-widest text-primary">VERSION / ATTESTATION</div>
            <h2 className="mt-1 font-mono text-sm font-bold tracking-widest">QUANTUMSHIELD {audit?.displayVersion ?? VERSION_LABEL_FALLBACK}</h2>
          </div>
          <button type="button" onClick={onClose} className="text-muted-foreground hover:text-foreground" data-testid="button-close-version-audit">
            <X className="w-4 h-4" />
          </button>
        </div>
        <div className="space-y-4 p-4 font-mono text-xs">
          {error && <div className="border border-destructive/40 bg-destructive/10 p-3 text-destructive">{error}</div>}
          {!audit && !error ? (
            <div className="text-muted-foreground">Loading version audit...</div>
          ) : audit ? (
            <>
              <div className={`border p-3 ${tone === "ok" ? "border-border/60 bg-muted/20 text-muted-foreground" : tone === "remote-behind" ? "border-amber-500/40 bg-amber-500/10 text-amber-500" : "border-destructive/40 bg-destructive/10 text-destructive"}`}>
                {statusCopy}
              </div>
              <div className="grid gap-2 sm:grid-cols-4">
                <div className={versionBoxClass}>
                  <div className="text-[10px] uppercase tracking-widest text-muted-foreground">client version</div>
                  <div className={versionValueClass}>{versionLabelForSnapshot(boot)}</div>
                  <div className={versionHashClass}>client {CLIENT_COMMIT}</div>
                </div>
                <div className={versionBoxClass}>
                  <div className="text-[10px] uppercase tracking-widest text-muted-foreground">server version</div>
                  <div className={versionValueClass}>{versionLabelForSnapshot(boot)}</div>
                  <div className={versionHashClass}>server {boot?.shortCommit ?? "unknown"}</div>
                </div>
                <div className={versionBoxClass}>
                  <div className="text-[10px] uppercase tracking-widest text-muted-foreground">local commit</div>
                  <div className={versionValueClass}>{versionLabelForSnapshot(current)}</div>
                  <div className={versionHashClass}>local {current?.shortCommit ?? "unknown"}</div>
                </div>
                <div className={versionBoxClass}>
                  <div className="text-[10px] uppercase tracking-widest text-muted-foreground">remote commit</div>
                  <div className={versionValueClass}>{current?.originMainDisplayVersion || boot?.originMainDisplayVersion || "unavailable"}</div>
                  <div className={versionHashClass}>remote {remoteCommit}</div>
                </div>
              </div>
              <div className="grid gap-2 sm:grid-cols-2">
                <AuditRow label="commit" value={`${boot?.shortCommit ?? "unknown"} / ${boot?.commitSubject ?? "unknown"}`} />
                <AuditRow label="package" value={audit.packageVersion} />
                <AuditRow label="mountain publish" value={formatAuditTime(publishUtc, "America/Denver")} />
                <AuditRow label="utc publish" value={formatAuditTime(publishUtc, "UTC")} />
                <AuditRow label="browser time" value={formatBrowserAuditTime(nowMs)} />
                <AuditRow label="elapsed since release" value={formatElapsedSince(publishUtc, nowMs)} />
                <AuditRow label="server boot" value={formatAuditTime(audit.serverStartedAtUtc, "UTC")} />
                <AuditRow label="origin/main match" value={audit.runningState.currentHeadMatchesOriginMain ? "yes" : "no"} />
              </div>
              <div className="grid gap-2">
                <AuditRow label="commit md5" value={boot?.commitMd5 ?? "unavailable"} mono />
                <AuditRow label="commit sha256" value={boot?.commitSha256 ?? "unavailable"} mono />
                <AuditRow label="tracked repo md5" value={boot?.repoMd5 ?? "unavailable"} mono />
                <AuditRow label="tracked repo sha256" value={boot?.repoSha256 ?? "unavailable"} mono />
                <AuditRow label="full commit" value={boot?.commit ?? "unavailable"} mono />
              </div>
              <div className="grid gap-2 sm:grid-cols-2">
                <AuditRow label="server runtime" value={`${audit.runtime.node} / ${audit.runtime.platform}-${audit.runtime.arch} / pid ${audit.runtime.pid}`} />
                <AuditRow label="server source attestation" value={audit.attestations.sourceIntegrity?.status ?? "unavailable"} />
                <AuditRow label="server hardware/os attestation" value={`${audit.attestations.serverHardwareOs?.status ?? "unavailable"}: ${audit.attestations.serverHardwareOs?.reason ?? ""}`} />
                <AuditRow label="client hardware/os attestation" value={`${audit.attestations.clientHardwareOs?.status ?? "unavailable"}: ${audit.attestations.clientHardwareOs?.reason ?? ""}`} />
              </div>
              <div className="border border-border/50 bg-background/50 p-3">
                <div className="mb-2 tracking-widest text-muted-foreground">CLIENT RUNTIME REPORT</div>
                <pre className="whitespace-pre-wrap break-all text-[10px] text-muted-foreground">{JSON.stringify(clientAttestation, null, 2)}</pre>
              </div>
              <div className="border border-border/50 bg-background/50 p-3">
                <div className="mb-2 tracking-widest text-muted-foreground">DIRTY FILES AT SERVER BOOT</div>
                <pre className="whitespace-pre-wrap break-all text-[10px] text-muted-foreground">{audit.git.boot.dirtySummary.length ? audit.git.boot.dirtySummary.join("\n") : "clean"}</pre>
              </div>
            </>
          ) : null}
        </div>
      </div>
    </div>
  );
}

function AuditRow({ label, value, mono = false }: { label: string; value: string; mono?: boolean }) {
  return (
    <div className="border border-border/50 bg-background/50 p-3">
      <div className="mb-1 text-[10px] tracking-widest text-muted-foreground">{label.toUpperCase()}</div>
      <div className={`break-all text-foreground ${mono ? "text-[10px]" : ""}`}>{value}</div>
    </div>
  );
}

function useOnlineStatus(): boolean {
  const [online, setOnline] = useState(true);
  useEffect(() => {
    let cancelled = false;
    const checkServer = async () => {
      const reachable = await apiReachable();
      if (!cancelled) setOnline(reachable);
    };
    const update = () => void checkServer();
    void checkServer();
    const interval = window.setInterval(checkServer, 15000);
    window.addEventListener("online", update);
    window.addEventListener("offline", update);
    return () => {
      cancelled = true;
      window.clearInterval(interval);
      window.removeEventListener("online", update);
      window.removeEventListener("offline", update);
    };
  }, []);
  return online;
}

async function apiReachable(timeoutMs = 2500): Promise<boolean> {
  try {
    const controller = new AbortController();
    const timeout = window.setTimeout(() => controller.abort(), timeoutMs);
    const response = await fetch("/api/healthz", { signal: controller.signal, cache: "no-store" });
    window.clearTimeout(timeout);
    return response.ok;
  } catch {
    return false;
  }
}

function readTrustedKeyBundles(): Record<string, string> {
  try {
    return JSON.parse(localStorage.getItem(KEY_BUNDLE_TRUST_KEY) ?? "{}") as Record<string, string>;
  } catch {
    return {};
  }
}

function writeTrustedKeyBundles(value: Record<string, string>): void {
  localStorage.setItem(KEY_BUNDLE_TRUST_KEY, JSON.stringify(value));
}

async function keyBundleFingerprint(bundle: KeyBundle): Promise<string> {
  const payload = new TextEncoder().encode(stableJson({
    v: 1,
    kemPublicKey: bundle.kemPublicKey ?? "",
    dsaPublicKey: bundle.dsaPublicKey ?? "",
    kemSignature: bundle.kemSignature ?? "",
  }));
  const digest = await crypto.subtle.digest("SHA-256", payload);
  return Array.from(new Uint8Array(digest), (byte) => byte.toString(16).padStart(2, "0")).join("");
}

async function trustFetchedKeyBundle(userId: string, bundle: KeyBundle): Promise<boolean> {
  if (!verifyKeyBundleSignature(bundle)) return false;
  const fingerprint = await keyBundleFingerprint(bundle);
  const trusted = readTrustedKeyBundles();
  const previous = trusted[userId];
  if (previous && previous !== fingerprint) {
    localStorage.setItem(KEY_BUNDLE_WARNING_KEY, JSON.stringify({
      userId,
      previous,
      current: fingerprint,
      detectedAt: new Date().toISOString(),
    }));
  }
  if (previous !== fingerprint) {
    trusted[userId] = fingerprint;
    writeTrustedKeyBundles(trusted);
  }
  await cacheTrustedKeyBundle({ userId, ...bundle, trustedAt: new Date().toISOString() });
  return true;
}

async function replaceTrustedKeyBundle(userId: string, bundle: KeyBundle): Promise<void> {
  if (!verifyKeyBundleSignature(bundle)) return;
  const trusted = readTrustedKeyBundles();
  trusted[userId] = await keyBundleFingerprint(bundle);
  writeTrustedKeyBundles(trusted);
  await cacheTrustedKeyBundle({ userId, ...bundle, trustedAt: new Date().toISOString() });
}

async function getTrustedKeyBundle(userId: string): Promise<KeyBundle | null> {
  try {
    const bundle = await getKeysUserId(userId);
    if (!(await trustFetchedKeyBundle(userId, bundle))) return null;
    return bundle;
  } catch {
    const cached = await getCachedTrustedKeyBundle(userId);
    if (!cached) return null;
    const bundle = {
      kemPublicKey: cached.kemPublicKey,
      dsaPublicKey: cached.dsaPublicKey,
      kemSignature: cached.kemSignature,
    };
    return verifyKeyBundleSignature(bundle) ? bundle : null;
  }
}

async function getTrustedKeyBundles(userId: string): Promise<KeyBundle[]> {
  try {
    const response = await fetch(`/api/keys/${encodeURIComponent(userId)}/devices`, {
      headers: getToken() ? { Authorization: `Bearer ${getToken()}` } : undefined,
    });
    if (!response.ok) throw new Error("No device key bundles found");
    const data = await response.json() as { bundles?: KeyBundle[] };
    const trusted: KeyBundle[] = [];
    const seenKemKeys = new Set<string>();
    for (const bundle of data.bundles ?? []) {
      if (!bundle.kemPublicKey || seenKemKeys.has(bundle.kemPublicKey)) continue;
      if (await trustFetchedKeyBundle(userId, bundle)) {
        trusted.push(bundle);
        seenKemKeys.add(bundle.kemPublicKey);
      }
    }
    if (trusted.length > 0) return trusted;
  } catch {
    // Fall through to the legacy latest-bundle/cache path.
  }
  const bundle = await getTrustedKeyBundle(userId);
  return bundle ? [bundle] : [];
}

async function aesGcmKeyFromBytes(bytes: Uint8Array): Promise<CryptoKey> {
  return crypto.subtle.importKey("raw", new Uint8Array(bytes).buffer as ArrayBuffer, { name: "AES-GCM", length: 256 }, false, ["encrypt", "decrypt"]);
}

function encodeWrappedKeys(values: string[]): RecipientEncryptedKeyValue | null {
  const unique = [...new Set(values.filter(Boolean))];
  if (unique.length === 0) return null;
  return unique.length === 1 ? unique[0] : unique;
}

function recipientEncryptedKeySignatureVariants(keys: RecipientEncryptedKeys): RecipientEncryptedKeys[] {
  const variants: RecipientEncryptedKeys[] = [keys];
  const seen = new Set([JSON.stringify(keys)]);

  const addVariant = (variant: RecipientEncryptedKeys) => {
    const fingerprint = JSON.stringify(variant);
    if (!seen.has(fingerprint)) {
      seen.add(fingerprint);
      variants.push(variant);
    }
  };

  const parsedArrays: RecipientEncryptedKeys = {};
  let parsedArraysChanged = false;
  for (const [userId, value] of Object.entries(keys)) {
    if (typeof value === "string") {
      try {
        const parsed = JSON.parse(value) as unknown;
        if (Array.isArray(parsed) && parsed.every((item) => typeof item === "string")) {
          parsedArrays[userId] = parsed;
          parsedArraysChanged = true;
          continue;
        }
      } catch {
        // Legacy single wrapped-key string.
      }
    }
    parsedArrays[userId] = value;
  }
  if (parsedArraysChanged) addVariant(parsedArrays);

  const stringifiedArrays: RecipientEncryptedKeys = {};
  let stringifiedArraysChanged = false;
  for (const [userId, value] of Object.entries(keys)) {
    if (Array.isArray(value)) {
      stringifiedArrays[userId] = JSON.stringify(value);
      stringifiedArraysChanged = true;
    } else {
      stringifiedArrays[userId] = value;
    }
  }
  if (stringifiedArraysChanged) addVariant(stringifiedArrays);

  return variants;
}

async function wrapMessageKeyForUserDevices(userId: string, rawMessageKey: Uint8Array): Promise<RecipientEncryptedKeyValue | null> {
  const bundles = await getTrustedKeyBundles(userId);
  const wrapped = await Promise.all(
    bundles.map((bundle) => bundle.kemPublicKey ? wrapMessageKeyForKemPublicKey(base64ToBytes(bundle.kemPublicKey), rawMessageKey) : null),
  );
  return encodeWrappedKeys(wrapped.filter((value): value is string => !!value));
}

async function wrapMessageKeyForCurrentUserDevices(userId: string, rawMessageKey: Uint8Array): Promise<RecipientEncryptedKeyValue | null> {
  const keys = await getLocalKeyPairAsync();
  try {
    const wrapped: string[] = [];
    if (keys.kemPublicKey && keys.kemSecretKey && localKemKeyPairCanRoundTrip(keys.kemPublicKey, keys.kemSecretKey)) {
      const localWrapped = await wrapMessageKeyForKemPublicKey(keys.kemPublicKey, rawMessageKey);
      if (localWrapped) wrapped.push(localWrapped);
    }
    const bundles = await getTrustedKeyBundles(userId);
    const localKemPublicKey = keys.kemPublicKey ? bytesToBase64(keys.kemPublicKey) : null;
    const remoteWrapped = await Promise.all(
      bundles
        .filter((bundle) => bundle.kemPublicKey && bundle.kemPublicKey !== localKemPublicKey)
        .map((bundle) => wrapMessageKeyForKemPublicKey(base64ToBytes(bundle.kemPublicKey!), rawMessageKey)),
    );
    wrapped.push(...remoteWrapped.filter((value): value is string => !!value));
    return encodeWrappedKeys(wrapped);
  } finally {
    clearBytes(keys.kemSecretKey);
    clearBytes(keys.dsaSecretKey);
  }
}

function localKemKeyPairCanRoundTrip(kemPublicKey: Uint8Array, kemSecretKey: Uint8Array): boolean {
  let sharedSecret: Uint8Array | null = null;
  let decapsulated: Uint8Array | null = null;
  try {
    const encapsulated = ml_kem1024.encapsulate(kemPublicKey);
    sharedSecret = encapsulated.sharedSecret;
    decapsulated = ml_kem1024.decapsulate(encapsulated.cipherText, kemSecretKey);
    return bytesToBase64(sharedSecret) === bytesToBase64(decapsulated);
  } catch {
    return false;
  } finally {
    clearBytes(sharedSecret);
    clearBytes(decapsulated);
  }
}

async function wrapMessageKeyForKemPublicKey(kemPublicKey: Uint8Array, rawMessageKey: Uint8Array): Promise<string | null> {
  let sharedSecret: Uint8Array | null = null;
  try {
    const encapsulated = ml_kem1024.encapsulate(kemPublicKey);
    sharedSecret = encapsulated.sharedSecret;
    const wrappingKey = await aesGcmKeyFromBytes(sharedSecret);
    const nonce = crypto.getRandomValues(new Uint8Array(12));
    const wrapped = await crypto.subtle.encrypt({ name: "AES-GCM", iv: nonce.buffer as ArrayBuffer }, wrappingKey, new Uint8Array(rawMessageKey).buffer as ArrayBuffer);
    return JSON.stringify({
      kemCiphertext: bytesToBase64(encapsulated.cipherText),
      nonce: bytesToBase64(nonce),
      wrappedKey: bytesToBase64(new Uint8Array(wrapped)),
    } satisfies WrappedMessageKey);
  } catch {
    return null;
  } finally {
    clearBytes(sharedSecret);
  }
}

async function signMessagePayload(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys: RecipientEncryptedKeys;
}): Promise<string | null> {
  const keys = await getLocalKeyPairAsync();
  if (!keys.dsaSecretKey) return null;
  try {
    const signature = ml_dsa87.sign(messageSignaturePayload(input), keys.dsaSecretKey);
    return bytesToBase64(signature);
  } finally {
    clearBytes(keys.kemSecretKey);
    clearBytes(keys.dsaSecretKey);
  }
}

async function senderDsaPublicKeyForSignedPayload(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys: RecipientEncryptedKeys;
  signature: string;
}): Promise<string | null> {
  const payload = messageSignaturePayload(input);
  for (const dsaPublicKey of await getDsaPublicKeysAsync()) {
    try {
      if (ml_dsa87.verify(base64ToBytes(input.signature), payload, base64ToBytes(dsaPublicKey))) return dsaPublicKey;
    } catch {
      // Try the next local signing key.
    }
  }
  return null;
}

async function verifyMessageSignature(roomId: string, msg: Message): Promise<boolean> {
  if (!msg.signature) return false;
  const verifyWithDsaPublicKey = (dsaPublicKey: string): boolean => {
    for (const recipientEncryptedKeys of recipientEncryptedKeySignatureVariants(msg.recipientEncryptedKeys ?? {})) {
      try {
        if (ml_dsa87.verify(
          base64ToBytes(msg.signature!),
          messageSignaturePayload({
            roomId,
            senderId: msg.senderId,
            ciphertext: msg.ciphertext,
            nonce: msg.nonce,
            algorithm: msg.algorithm,
            recipientEncryptedKeys,
          }),
          base64ToBytes(dsaPublicKey),
        )) {
          return true;
        }
      } catch {
        // Try the next migration variant or signing key.
      }
    }
    return false;
  };

  if (msg.senderDsaPublicKey) {
    if (verifyWithDsaPublicKey(msg.senderDsaPublicKey)) return true;
  }
  const localDsaPublicKey = getDsaPublicKey();
  if (localDsaPublicKey) {
    if (verifyWithDsaPublicKey(localDsaPublicKey)) return true;
  }
  for (const historicalDsaPublicKey of await getDsaPublicKeysAsync()) {
    if (historicalDsaPublicKey !== localDsaPublicKey && verifyWithDsaPublicKey(historicalDsaPublicKey)) return true;
  }
  try {
    const bundle = await getTrustedKeyBundle(msg.senderId);
    if (!bundle?.dsaPublicKey) return false;
    return verifyWithDsaPublicKey(bundle.dsaPublicKey);
  } catch {
    return false;
  }
}

function normalizeWrappedKeyCandidates(wrappedValue: RecipientEncryptedKeyValue): string[] {
  if (Array.isArray(wrappedValue)) return wrappedValue;
  try {
    const parsed = JSON.parse(wrappedValue) as unknown;
    if (Array.isArray(parsed) && parsed.every((item) => typeof item === "string")) return parsed;
  } catch {
    // Legacy single wrapped-key string.
  }
  return [wrappedValue];
}

async function unwrapSingleMessageKeyForMe(wrappedValue: string, kemSecretKeys: Uint8Array[]): Promise<CryptoKey | null> {
  let sharedSecret: Uint8Array | null = null;
  let rawKey: Uint8Array | null = null;
  try {
    const wrapped = JSON.parse(wrappedValue) as WrappedMessageKey;
    for (const kemSecretKey of kemSecretKeys) {
      try {
        sharedSecret = ml_kem1024.decapsulate(base64ToBytes(wrapped.kemCiphertext), kemSecretKey);
        const wrappingKey = await aesGcmKeyFromBytes(sharedSecret);
        const decryptedRawKey = await crypto.subtle.decrypt(
          { name: "AES-GCM", iv: base64ToBytes(wrapped.nonce).buffer as ArrayBuffer },
          wrappingKey,
          base64ToBytes(wrapped.wrappedKey).buffer as ArrayBuffer
        );
        rawKey = new Uint8Array(decryptedRawKey);
        return importMessageKey(rawKey);
      } catch {
        clearBytes(sharedSecret);
        sharedSecret = null;
      }
    }
    return null;
  } catch {
    return null;
  } finally {
    clearBytes(sharedSecret);
    clearBytes(rawKey);
  }
}

async function unwrapMessageKeyForMe(wrappedValue: RecipientEncryptedKeyValue): Promise<CryptoKey | null> {
  const kemSecretKeys = await getKemSecretKeysAsync();
  if (kemSecretKeys.length === 0) return null;
  try {
    for (const candidate of normalizeWrappedKeyCandidates(wrappedValue)) {
      const key = await unwrapSingleMessageKeyForMe(candidate, kemSecretKeys);
      if (key) return key;
    }
    return null;
  } finally {
    for (const kemSecretKey of kemSecretKeys) clearBytes(kemSecretKey);
  }
}

type Room = {
  id: string;
  name?: string | null;
  type: "direct" | "group";
  memberCount: number;
  lastMessageAt?: string | null;
  ttlSeconds?: number | null;
  ttlMode?: "after_view" | "after_send";
  deliveryFuzzSeconds?: number | null;
  decayMode?: "standard" | "experimental_quorum_decay" | null;
  members?: Array<{ id: string; username: string; displayName?: string | null; avatarColor?: string | null }> | null;
};

type Message = {
  id: string;
  roomId?: string | null;
  senderId: string;
  senderUsername?: string | null;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  signature?: string | null;
  senderDsaPublicKey?: string | null;
  recipientEncryptedKeys?: RecipientEncryptedKeys | null;
  expiresAt?: string | null;
  decayedAt?: string | null;
  decayAttestation?: Record<string, unknown> | null;
  availableAt?: string | null;
  createdAt: string;
  localQueued?: boolean;
  localFuzzing?: boolean;
  localOptimistic?: boolean;
};

type WrappedMessageKey = {
  kemCiphertext: string;
  nonce: string;
  wrappedKey: string;
};

function outboxEntryToMessage(entry: OfflineOutboxEntry, senderId: string): Message {
  return {
    id: `offline:${entry.id}`,
    roomId: entry.roomId,
    senderId,
    senderUsername: null,
    ciphertext: entry.ciphertext,
    nonce: entry.nonce,
    algorithm: entry.algorithm,
    signature: entry.signature,
    senderDsaPublicKey: entry.senderDsaPublicKey ?? getDsaPublicKey(),
    recipientEncryptedKeys: entry.recipientEncryptedKeys,
    expiresAt: null,
    availableAt: entry.availableAt ?? entry.createdAt,
    createdAt: entry.createdAt,
    localQueued: true,
  };
}

function localSentMessage(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  signature: string;
  recipientEncryptedKeys: RecipientEncryptedKeys;
  createdAt: string;
  localFuzzing: boolean;
}): Message {
  return {
    id: `local-sent-${crypto.randomUUID()}`,
    roomId: input.roomId,
    senderId: input.senderId,
    senderUsername: null,
    ciphertext: input.ciphertext,
    nonce: input.nonce,
    algorithm: input.algorithm,
    signature: input.signature,
    senderDsaPublicKey: getDsaPublicKey(),
    recipientEncryptedKeys: input.recipientEncryptedKeys,
    decayAttestation: null,
    decayedAt: null,
    expiresAt: null,
    availableAt: input.createdAt,
    createdAt: input.createdAt,
    localFuzzing: input.localFuzzing,
    localOptimistic: true,
  };
}

function stableJson(value: unknown): string {
  if (Array.isArray(value)) return `[${value.map(stableJson).join(",")}]`;
  if (value && typeof value === "object") {
    return `{${Object.keys(value as Record<string, unknown>)
      .sort()
      .map((key) => `${JSON.stringify(key)}:${stableJson((value as Record<string, unknown>)[key])}`)
      .join(",")}}`;
  }
  return JSON.stringify(value);
}

function messageSignaturePayload(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys?: RecipientEncryptedKeys | null;
}): Uint8Array {
  return new TextEncoder().encode(
    stableJson({
      v: 1,
      purpose: "quantumshield.chat.message",
      roomId: input.roomId,
      senderId: input.senderId,
      ciphertext: input.ciphertext,
      nonce: input.nonce,
      algorithm: input.algorithm,
      recipientEncryptedKeys: input.recipientEncryptedKeys ?? {},
    })
  );
}

function verifyKeyBundleSignature(bundle: { kemPublicKey?: string | null; dsaPublicKey?: string | null; kemSignature?: string | null }): boolean {
  if (!bundle.kemPublicKey || !bundle.dsaPublicKey || !bundle.kemSignature) return false;
  try {
    return ml_dsa87.verify(base64ToBytes(bundle.kemSignature), base64ToBytes(bundle.kemPublicKey), base64ToBytes(bundle.dsaPublicKey));
  } catch {
    return false;
  }
}

function getRoomLabel(room: Room, currentUserId?: string): string {
  if (room.name) return room.name;
  if (room.type === "direct" && room.members) {
    const other = room.members.find((m) => m.id !== currentUserId);
    return other?.displayName ?? other?.username ?? "Direct Message";
  }
  return `Group (${room.memberCount})`;
}

const CODE_NAMES = [
  "Axiom", "Beacon", "Cipher", "Delta", "Echo", "Flux", "Grid", "Halo",
  "Ion", "Junction", "Keystone", "Lumen", "Matrix", "Nova", "Obsidian", "Pulse",
  "Quartz", "Relay", "Signal", "Trace", "Unit", "Vector", "Ward", "Zenith",
];

const DEFAULT_DELIVERY_FUZZ_SECONDS = 89;
const DELIVERY_FUZZ_OPTIONS = [
  { label: "No fuzzing", value: 0 },
  { label: "14 sec", value: 14 },
  { label: "89 sec", value: 89 },
  { label: "7 minutes", value: 420 },
  { label: "28 minutes", value: 1680 },
  { label: "73 minutes", value: 4380 },
  { label: "5h 47m", value: 20820 },
  { label: "29 hours", value: 104400 },
  { label: "8d 3h", value: 702000 },
  { label: "33 days", value: 2851200 },
  { label: "409 days", value: 35337600 },
];

function formatShortDuration(seconds: number): string {
  const safeSeconds = Math.max(0, Math.floor(seconds));
  if (safeSeconds < 120) return `${safeSeconds}s`;
  if (safeSeconds < 3600) {
    const minutes = Math.floor(safeSeconds / 60);
    const remainingSeconds = safeSeconds % 60;
    return remainingSeconds ? `${minutes}m ${remainingSeconds}s` : `${minutes}m`;
  }
  if (safeSeconds < 86400) {
    const hours = Math.floor(safeSeconds / 3600);
    const minutes = Math.floor((safeSeconds % 3600) / 60);
    return minutes ? `${hours}h ${minutes}m` : `${hours}h`;
  }
  return `${Math.round(safeSeconds / 86400)}d`;
}

function incompatibleFuzzWarning(ttlSeconds: number | null, ttlMode: "after_view" | "after_send", deliveryFuzzSeconds: number): string | null {
  if (!ttlSeconds || ttlMode !== "after_send" || deliveryFuzzSeconds <= ttlSeconds) return null;
  return `Delivery fuzz is ${formatShortDuration(deliveryFuzzSeconds)}, but the send timer is ${formatShortDuration(ttlSeconds)}. Some messages may expire before recipients can receive or reveal them.`;
}

function randomRefetchInterval(minMs: number, maxMs: number): number {
  return minMs + Math.floor(Math.random() * (maxMs - minMs + 1));
}

function createSessionCodenameFactory() {
  const names = [...CODE_NAMES];
  const random = new Uint32Array(names.length);
  crypto.getRandomValues(random);
  for (let i = names.length - 1; i > 0; i--) {
    const j = random[i] % (i + 1);
    [names[i], names[j]] = [names[j], names[i]];
  }

  const assigned = new Map<string, string>();
  let cursor = 0;

  return (id: string) => {
    const existing = assigned.get(id);
    if (existing) return existing;
    const label = `${names[cursor % names.length]}-${String(cursor + 1).padStart(2, "0")}`;
    cursor += 1;
    assigned.set(id, label);
    return label;
  };
}

function CameraScanStatus({
  status,
  detail,
}: {
  status: "scanning" | "clear" | "threat" | "unavailable";
  detail: string;
}) {
  const [open, setOpen] = useState(false);
  const cfg = {
    scanning: { dot: "bg-muted-foreground/60", text: "text-muted-foreground", label: "STARTING PRIVACY SCAN" },
    clear: { dot: "bg-primary animate-pulse", text: "text-primary", label: "PRIVACY ENSURED" },
    threat: { dot: "bg-destructive animate-pulse", text: "text-destructive", label: "RECORDING DEVICE DETECTED" },
    unavailable: { dot: "bg-muted-foreground/40", text: "text-muted-foreground", label: "PRIVACY SCAN OFFLINE" },
  }[status];
  return (
    <div className="relative border-b border-border/50 flex-shrink-0" data-testid="camera-status">
      <button
        type="button"
        onClick={() => setOpen((value) => !value)}
        className="w-full px-4 py-1.5 flex items-center gap-2 text-left"
        aria-expanded={open}
      >
        <span className={`w-1.5 h-1.5 rounded-full ${cfg.dot} flex-shrink-0`} />
        <span className={`font-mono text-[10px] tracking-widest ${cfg.text}`}>
          {cfg.label}{detail ? ` / ${detail}` : ""}
        </span>
      </button>
      {open && (
        <div className="absolute left-4 right-4 top-full z-50 mt-2 border border-primary/30 bg-background/95 p-4 shadow-xl backdrop-blur">
          <p className="font-mono text-xs tracking-widest text-primary mb-2">WHY THE CAMERA IS ON</p>
          <p className="font-mono text-xs text-muted-foreground leading-relaxed">
            QuantumShield uses your front camera locally to look for nearby recording devices pointed at the screen and sudden screen-flash reflections that may indicate a screenshot. Frames are processed on this device for privacy-shield decisions and are not uploaded or attached to messages.
          </p>
        </div>
      )}
    </div>
  );
}

function formatTime(iso: string): string {
  const d = new Date(iso);
  return d.toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
}

function formatDate(iso: string): string {
  const d = new Date(iso);
  const now = new Date();
  const isToday = d.toDateString() === now.toDateString();
  if (isToday) return formatTime(iso);
  return d.toLocaleDateString([], { month: "short", day: "numeric" });
}

function formatLongDuration(seconds: number): string {
  const safeSeconds = Math.max(0, Math.floor(seconds));
  const days = Math.floor(safeSeconds / 86400);
  const hours = Math.floor((safeSeconds % 86400) / 3600);
  const minutes = Math.floor((safeSeconds % 3600) / 60);
  const remainingSeconds = safeSeconds % 60;
  const parts: string[] = [];
  if (days) parts.push(`${days} day${days === 1 ? "" : "s"}`);
  if (hours) parts.push(`${hours} hour${hours === 1 ? "" : "s"}`);
  if (minutes) parts.push(`${minutes} minute${minutes === 1 ? "" : "s"}`);
  if (remainingSeconds || parts.length === 0) parts.push(`${remainingSeconds} second${remainingSeconds === 1 ? "" : "s"}`);
  return parts.slice(0, 2).join(" ");
}

function latestFuzzDeliveryLabel(sentAt: string, fuzzSeconds: number | null | undefined, nowMs: number): string | null {
  if (!fuzzSeconds || fuzzSeconds <= 0) return null;
  const sentMs = new Date(sentAt).getTime();
  if (!Number.isFinite(sentMs)) return null;
  const latestMs = sentMs + fuzzSeconds * 1000;
  if (latestMs <= nowMs) return null;
  const remainingSeconds = Math.ceil((latestMs - nowMs) / 1000);
  const latest = new Date(latestMs);
  return `${formatLongDuration(fuzzSeconds)} or by ${latest.toLocaleString([], {
    month: "short",
    day: "numeric",
    hour: "numeric",
    minute: "2-digit",
  })}. Remaining: ${formatLongDuration(remainingSeconds)}`;
}

function isWithinFuzzWindow(sentAt: string, fuzzSeconds: number | null | undefined, nowMs: number): boolean {
  if (!fuzzSeconds || fuzzSeconds <= 0) return false;
  const sentMs = new Date(sentAt).getTime();
  return Number.isFinite(sentMs) && nowMs < sentMs + fuzzSeconds * 1000;
}

function sameSentMessage(local: Message, live: Message): boolean {
  return (local.signature ? live.signature === local.signature : false) || live.ciphertext === local.ciphertext;
}

function messageBelongsToRoom(message: Message, roomId: string): boolean {
  return !message.roomId || message.roomId === roomId;
}

function shouldKeepFuzzMetadata(local: Message, fuzzSeconds: number | null | undefined, nowMs: number): boolean {
  return !!local.localFuzzing && isWithinFuzzWindow(local.createdAt, Math.max(1, fuzzSeconds ?? 0), nowMs);
}

function TTLLabel({ seconds, mode }: { seconds?: number | null; mode?: "after_view" | "after_send" }) {
  if (!seconds) return null;
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const label = `${h > 0 ? `${h}h` : `${m}m`} ${mode === "after_send" ? "after send" : "after view"}`;
  return (
    <span className="font-mono text-xs text-primary/60 flex items-center gap-1">
      <Clock className="w-3 h-3" />
      {label}
    </span>
  );
}

function DecayModeLabel({ mode }: { mode?: Room["decayMode"] }) {
  const experimental = mode === "experimental_quorum_decay";
  return (
    <span className={`font-mono text-[10px] md:text-xs flex items-center gap-1 ${experimental ? "text-amber-500" : "text-muted-foreground"}`}>
      <Shield className="w-3 h-3" />
      {experimental ? "QUORUM DECAY ACTIVE" : "DECAY STANDARD"}
    </span>
  );
}

function FuzzLabel({ seconds }: { seconds?: number | null }) {
  if (!seconds || seconds <= 0) return null;
  return (
    <span className="font-mono text-xs text-amber-500/80 flex items-center gap-1">
      <Clock className="w-3 h-3" />
      fuzz {formatShortDuration(seconds)}
    </span>
  );
}

function ChatMetaRows({ room, revealed }: { room: Room; revealed: boolean }) {
  return (
    <div className="mt-1 space-y-0.5 min-w-0">
      <div className="flex items-center gap-2 min-w-0">
        <Shield className="w-3 h-3 text-primary flex-shrink-0" />
        <span className="font-mono text-[10px] md:text-xs text-primary truncate">{CIPHER_SUITE}</span>
      </div>
      {room.ttlSeconds && (
        <div className="flex items-center gap-2 min-w-0">
          <TTLLabel seconds={room.ttlSeconds} mode={room.ttlMode} />
        </div>
      )}
      {revealed && !!room.deliveryFuzzSeconds && room.deliveryFuzzSeconds > 0 && (
        <div className="flex items-center gap-2 min-w-0">
          <FuzzLabel seconds={room.deliveryFuzzSeconds} />
        </div>
      )}
      <div className="flex items-center gap-2 min-w-0">
        {revealed ? (
          <DecayModeLabel mode={room.decayMode} />
        ) : (
          <span className="font-mono text-[10px] md:text-xs text-muted-foreground flex items-center gap-1">
            <Shield className="w-3 h-3" />
            DECAY SEALED
          </span>
        )}
      </div>
    </div>
  );
}

function hashString32(value: string): number {
  let hash = 2166136261;
  for (let i = 0; i < value.length; i++) {
    hash ^= value.charCodeAt(i);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function deterministicGarbledPreview(msg: Message): string {
  const alphabet = "0123456789abcdef!?/\\|#$%&";
  const seed = stableJson({
    id: msg.id,
    expiresAt: msg.expiresAt ?? "",
    decayedAt: msg.decayedAt ?? "",
    decayAttestation: msg.decayAttestation ?? null,
    ciphertext: msg.ciphertext,
  });
  let state = hashString32(seed);
  const chunks: string[] = [];
  for (let i = 0; i < 4; i++) {
    let chunk = "";
    for (let j = 0; j < 8; j++) {
      state = Math.imul(state ^ (state >>> 15), 2246822507) >>> 0;
      chunk += alphabet[state % alphabet.length];
    }
    chunks.push(chunk);
  }
  return chunks.join(" ");
}

function isLegacySignatureGraceMessage(msg: Message): boolean {
  const createdAtMs = new Date(msg.createdAt).getTime();
  return Number.isFinite(createdAtMs) && createdAtMs < LEGACY_SIGNATURE_GRACE_BEFORE_MS;
}

function getDecayEvidence(msg: Message, nowMs: number): { active: boolean; expired: boolean; text: string } {
  const expiresAtMs = msg.expiresAt ? new Date(msg.expiresAt).getTime() : Number.POSITIVE_INFINITY;
  const decayedAtMs = msg.decayedAt ? new Date(msg.decayedAt).getTime() : Number.POSITIVE_INFINITY;
  const expired = Number.isFinite(expiresAtMs) && expiresAtMs <= nowMs;
  const decayed = Number.isFinite(decayedAtMs) && decayedAtMs <= nowMs;
  const approaching = Number.isFinite(expiresAtMs) && expiresAtMs > nowMs && expiresAtMs - nowMs <= 30000;
  const attested = !!msg.decayAttestation;
  const active = expired || decayed || approaching;
  const text = decayed
    ? "DECAYED"
    : expired
      ? "EXPIRED"
      : approaching
        ? "DECAY IMMINENT"
        : attested
          ? "DECAY ATTESTED"
          : "SEALED";
  return { active, expired: expired || decayed, text };
}

function MessageExpiry({ expiresAt, revealed }: { expiresAt: string | null | undefined; revealed: boolean }) {
  const [remaining, setRemaining] = useState("");

  useEffect(() => {
    if (!expiresAt) return;
    const update = () => {
      const diff = new Date(expiresAt).getTime() - Date.now();
      if (diff <= 0) {
        setRemaining("EXPIRED");
        return;
      }
      const m = Math.floor(diff / 60000);
      const s = Math.floor((diff % 60000) / 1000);
      setRemaining(`${m}:${String(s).padStart(2, "0")}`);
    };
    update();
    const i = setInterval(update, 1000);
    return () => clearInterval(i);
  }, [expiresAt]);

  if (!expiresAt) return null;
  return (
    <span className="font-mono text-xs text-muted-foreground flex items-center gap-1">
      <Clock className="w-3 h-3" />
      {revealed ? remaining : "TTL SEALED"}
    </span>
  );
}

function NewRoomDialog({
  onClose,
  currentUserId,
  codenameForUser,
}: {
  onClose: () => void;
  currentUserId: string;
  codenameForUser: (id: string) => string;
}) {
  const qc = useQueryClient();
  const [name, setName] = useState("");
  const [type, setType] = useState<"direct" | "group">("direct");
  const [ttl, setTtl] = useState<number | null>(300);
  const [ttlMode, setTtlMode] = useState<"after_view" | "after_send">("after_view");
  const [deliveryFuzzSeconds, setDeliveryFuzzSeconds] = useState(DEFAULT_DELIVERY_FUZZ_SECONDS);
  const [decayMode, setDecayMode] = useState<"standard" | "experimental_quorum_decay">("standard");
  const [pendingTtlMode, setPendingTtlMode] = useState<"after_view" | "after_send" | null>(null);
  const [search, setSearch] = useState("");
  const [searchHash, setSearchHash] = useState("");
  const [selectedIds, setSelectedIds] = useState<string[]>([]);
  const [revealedUserId, setRevealedUserId] = useState<string | null>(null);
  const settingsWarning = incompatibleFuzzWarning(ttl, ttlMode, deliveryFuzzSeconds);

  const normalizedSearch = normalizeCodeInput(search);
  useEffect(() => {
    let cancelled = false;
    if (!normalizedSearch) {
      setSearchHash("");
      return;
    }
    hashIdentityCode(normalizedSearch).then((hash) => {
      if (!cancelled) setSearchHash(hash);
    });
    return () => { cancelled = true; };
  }, [normalizedSearch]);

  const { data: searchResults } = useGetUsersSearch(
    { q: searchHash },
    { query: { queryKey: getGetUsersSearchQueryKey({ q: searchHash }), enabled: searchHash.length > 0 } }
  );

  const createRoom = usePostRooms({
    mutation: {
      onSuccess: () => {
        qc.invalidateQueries({ queryKey: getGetRoomsQueryKey() });
        onClose();
      },
    },
  });

  const toggleUser = (id: string) => {
    setSelectedIds((prev) => (prev.includes(id) ? prev.filter((x) => x !== id) : [...prev, id]));
  };

  const handleCreate = () => {
    createRoom.mutate({
      data: {
        name: name || null,
        type,
        memberIds: selectedIds,
        ttlSeconds: ttl,
        ttlMode,
        deliveryFuzzSeconds,
        decayMode,
      },
    });
  };

  const TTL_OPTIONS = [
    { label: "No expiry", value: null },
    { label: "5 minutes", value: 300 },
    { label: "1 hour", value: 3600 },
    { label: "24 hours", value: 86400 },
    { label: "7 days", value: 604800 },
  ];

  return (
    <div className="fixed inset-0 bg-background/80 backdrop-blur-sm z-50 flex items-center justify-center p-4">
      <div className="w-full max-w-md border border-border bg-card p-6">
        <div className="flex items-center justify-between mb-6">
          <h2 className="font-mono font-bold tracking-tight">NEW ENCRYPTED CHANNEL</h2>
          <button onClick={onClose} className="text-muted-foreground hover:text-foreground" data-testid="button-close-dialog">
            <X className="w-4 h-4" />
          </button>
        </div>

        <div className="space-y-4">
          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">CHANNEL NAME (OPTIONAL)</label>
            <input
              value={name}
              onChange={(e) => setName(e.target.value)}
              className="w-full bg-background border border-border px-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
              placeholder="Channel name..."
              data-testid="input-room-name"
            />
          </div>

          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">TYPE</label>
            <div className="flex gap-2">
              {(["direct", "group"] as const).map((t) => (
                <button
                  key={t}
                  onClick={() => setType(t)}
                  className={`flex-1 py-2 font-mono text-xs tracking-widest border transition-all ${
                    type === t ? "bg-primary text-primary-foreground border-primary" : "border-border text-muted-foreground hover:border-primary/50"
                  }`}
                  data-testid={`button-type-${t}`}
                >
                  {t.toUpperCase()}
                </button>
              ))}
            </div>
          </div>

          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">MESSAGE EXPIRY (TTL)</label>
            <select
              value={ttl ?? ""}
              onChange={(e) => setTtl(e.target.value ? Number(e.target.value) : null)}
              className="w-full bg-background border border-border px-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
              data-testid="select-ttl"
            >
              {TTL_OPTIONS.map((o) => (
                <option key={String(o.value)} value={o.value ?? ""}>{o.label}</option>
              ))}
            </select>
          </div>

          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">TTL STARTS</label>
            <div className="grid grid-cols-2 gap-2">
              {[
                { value: "after_view" as const, label: "AFTER VIEW" },
                { value: "after_send" as const, label: "AFTER SEND" },
              ].map((mode) => (
                <button
                  key={mode.value}
                  type="button"
                  onClick={() => mode.value !== ttlMode && setPendingTtlMode(mode.value)}
                  className={`border px-3 py-2 font-mono text-xs ${ttlMode === mode.value ? "border-primary bg-primary/10 text-primary" : "border-border text-muted-foreground hover:border-primary/50"}`}
                >
                  {mode.label}
                </button>
              ))}
            </div>
          </div>

          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">DELIVERY FUZZ</label>
            <select
              value={deliveryFuzzSeconds}
              onChange={(e) => setDeliveryFuzzSeconds(Number(e.target.value))}
              className="w-full bg-background border border-border px-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
              data-testid="select-delivery-fuzz"
            >
              {DELIVERY_FUZZ_OPTIONS.map((option) => (
                <option key={option.value} value={option.value}>{option.label}</option>
              ))}
            </select>
            <p className="font-mono text-xs text-muted-foreground mt-1">Server releases each message at a random time inside this window. Default is 89 seconds.</p>
          </div>

          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">DECAY TIER</label>
            <div className="grid grid-cols-2 gap-2">
              {[
                { value: "standard" as const, label: "STANDARD" },
                { value: "experimental_quorum_decay" as const, label: "EXPERIMENTAL" },
              ].map((option) => (
                <button
                  key={option.value}
                  type="button"
                  onClick={() => setDecayMode(option.value)}
                  className={`border px-3 py-2 font-mono text-xs ${
                    decayMode === option.value ? "border-amber-500 bg-amber-500/10 text-amber-500" : "border-border text-muted-foreground hover:border-amber-500/50"
                  }`}
                  data-testid={`button-decay-mode-${option.value}`}
                >
                  {option.label}
                </button>
              ))}
            </div>
            {decayMode === "experimental_quorum_decay" && (
              <p className="font-mono text-xs text-amber-500 mt-1">
                Multiple clocks must attest the time so even if a device, server, or stored keys are compromised after expiry, messages decay. Uses device time, server time, and multiple public clocks.
              </p>
            )}
          </div>

          {settingsWarning && (
            <div className="border border-destructive/40 bg-destructive/10 px-3 py-2 flex items-start gap-2" data-testid="room-settings-warning">
              <AlertTriangle className="w-4 h-4 text-destructive mt-0.5 flex-shrink-0" />
              <p className="font-mono text-xs leading-relaxed text-destructive">{settingsWarning}</p>
            </div>
          )}

          <div>
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">ADD MEMBERS</label>
            <div className="relative">
              <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-3.5 h-3.5 text-muted-foreground" />
              <input
                value={search}
                onChange={(e) => setSearch(e.target.value)}
                className="w-full bg-background border border-border pl-8 pr-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
                placeholder="Search code..."
                data-testid="input-search-users"
              />
            </div>

            {searchResults && searchResults.length > 0 && (
              <div className="border border-border mt-1 max-h-32 overflow-y-auto">
                {searchResults
                  .filter((u) => u.id !== currentUserId)
                  .map((u) => {
                    const visibleName = revealedUserId === u.id ? (u.displayName ?? u.username) : codenameForUser(u.id);
                    return (
                      <button
                        key={u.id}
                        onClick={() => toggleUser(u.id)}
                        onPointerDown={() => setRevealedUserId(u.id)}
                        onPointerUp={() => setRevealedUserId(null)}
                        onPointerCancel={() => setRevealedUserId(null)}
                        onPointerLeave={() => setRevealedUserId(null)}
                        className={`w-full flex items-center gap-2 px-3 py-2 font-mono text-xs hover:bg-accent transition-colors text-left ${
                          selectedIds.includes(u.id) ? "bg-primary/10 text-primary" : ""
                        }`}
                        data-testid={`button-user-${u.id}`}
                      >
                        <div
                          className="w-5 h-5 rounded-full flex items-center justify-center text-white text-xs font-bold"
                          style={{ backgroundColor: u.avatarColor ?? "#06b6d4" }}
                        >
                          {codenameForUser(u.id)[0]}
                        </div>
                        {visibleName}
                        {selectedIds.includes(u.id) && <span className="ml-auto text-primary">SELECTED</span>}
                      </button>
                    );
                  })}
              </div>
            )}

            {selectedIds.length > 0 && (
              <p className="font-mono text-xs text-primary mt-2">{selectedIds.length} member(s) selected</p>
            )}
          </div>

          <button
            onClick={handleCreate}
            disabled={createRoom.isPending}
            className="w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-3 hover:bg-primary/90 disabled:opacity-50"
            data-testid="button-create-room"
          >
            {createRoom.isPending ? "CREATING..." : "CREATE ENCRYPTED CHANNEL"}
          </button>
        </div>
      </div>
      {pendingTtlMode && (
        <div className="fixed inset-0 z-[60] bg-background/90 backdrop-blur-sm flex items-center justify-center p-4">
          <div className="w-full max-w-md border border-border bg-card p-5 shadow-2xl">
            <div className="font-mono text-xs tracking-widest text-primary mb-3">EXPIRY MODE</div>
            <h3 className="font-mono text-lg font-bold mb-2">
              {pendingTtlMode === "after_view" ? "Start TTL after first view?" : "Start TTL after send?"}
            </h3>
            <p className="font-mono text-xs text-muted-foreground leading-relaxed">
              {pendingTtlMode === "after_view"
                ? "Messages stay available until the room is opened and fetched, then the countdown starts. This is the default for ephemeral conversations."
                : "Messages begin expiring immediately when sent, even if nobody has viewed them yet."}
            </p>
            <div className="grid grid-cols-2 gap-2 mt-5">
              <button type="button" onClick={() => setPendingTtlMode(null)} className="border border-border px-3 py-2.5 font-mono text-xs hover:border-primary/50">
                CANCEL
              </button>
              <button
                type="button"
                onClick={() => {
                  setTtlMode(pendingTtlMode);
                  setPendingTtlMode(null);
                }}
                className="bg-primary text-primary-foreground px-3 py-2.5 font-mono text-xs"
              >
                USE MODE
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}

const CODE_TTL_OPTIONS = [
  { label: "5 minutes", value: 300 },
  { label: "1 hour", value: 3600 },
  { label: "1 day", value: 86400 },
  { label: "1 month", value: 2592000 },
  { label: "1 year", value: 31536000 },
  { label: "10 years", value: 315360000 },
];

const CODE_SCOPE_OPTIONS = [
  { label: "Public", value: "public" },
  { label: "People I invited", value: "invited_by_you" },
  { label: "People who invited me", value: "invited_you" },
  { label: "Mutuals", value: "mutuals" },
  { label: "Disabled", value: "disabled" },
] as const;

function describeCodeKind(kind: "alias" | "invite"): string {
  return kind === "alias"
    ? "Your readable handle stays local. The server stores a peppered exact-lookup value so people can find you only by typing the exact handle."
    : "An invite is a public one-use code. Share it with one person or device, and it stops working after it is used, expired, or rolled.";
}

function displayIdentityCode(code: IdentityCode, unsealedHandles: Record<string, string> = {}): string {
  const unsealed = unsealedHandles[code.id];
  return code.kind === "alias" ? (unsealed ? `@${unsealed}` : "SEALED HANDLE") : `#${code.code}`;
}

function formatExpiry(expiresAt?: string | null): string {
  if (!expiresAt) return "No expiration";
  const expiry = new Date(expiresAt);
  const diff = expiry.getTime() - Date.now();
  const abs = expiry.toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" });
  if (diff <= 0) return `${abs} / expired`;
  const minutes = Math.floor(diff / 60000);
  const days = Math.floor(minutes / 1440);
  const hours = Math.floor((minutes % 1440) / 60);
  const mins = minutes % 60;
  const remaining = days > 0 ? `${days}d ${hours}h remaining` : hours > 0 ? `${hours}h ${mins}m remaining` : `${mins}m remaining`;
  return `${abs} / ${remaining}`;
}

type DeviceSession = {
  id: string;
  label: string;
  current: boolean;
  createdAt: string;
  expiresAt: string;
};

function formatSessionTime(value: string): string {
  return new Date(value).toLocaleString(undefined, { dateStyle: "medium", timeStyle: "short" });
}

function useDeviceSessions(enabled: boolean, refreshKey = 0) {
  const [sessions, setSessions] = useState<DeviceSession[] | null>(null);

  useEffect(() => {
    if (!enabled) return;
    let mounted = true;
    const token = getToken();
    if (!token) return;
    fetch("/api/auth/devices", {
      headers: { Authorization: `Bearer ${token}` },
    })
      .then((res) => (res.ok ? res.json() : null))
      .then((data) => {
        if (mounted && data && Array.isArray(data.sessions)) {
          setSessions(data.sessions as DeviceSession[]);
        }
      })
      .catch(() => {
        if (mounted) setSessions(null);
      });
    return () => {
      mounted = false;
    };
  }, [enabled, refreshKey]);

  return sessions;
}

function ProfilePanel({
  onClose,
  me,
  codename,
}: {
  onClose: () => void;
  me: { id: string; username: string; displayName?: string | null; avatarColor?: string | null };
  codename: string;
}) {
  const qc = useQueryClient();
  const [, setLocation] = useLocation();
  const isMobile = useIsMobile();
  const [revealed, setRevealed] = useState(false);
  const [newCode, setNewCode] = useState("");
  const [newKind, setNewKind] = useState<"alias" | "invite">("alias");
  const [newTtl, setNewTtl] = useState<number>(315360000);
  const [unsealHandle, setUnsealHandle] = useState("");
  const [unsealStatus, setUnsealStatus] = useState<{ tone: "ok" | "error"; text: string } | null>(null);
  const [unsealedHandles, setUnsealedHandles] = useState<Record<string, string>>(() => getUnsealedHandleLabels());
  const [error, setError] = useState("");
  const [passkeyStatus, setPasskeyStatus] = useState<{ tone: "ok" | "error"; text: string } | null>(null);
  const [passkeyPending, setPasskeyPending] = useState(false);
  const [sessionActionStatus, setSessionActionStatus] = useState<{ tone: "ok" | "error"; text: string } | null>(null);
  const [sessionActionPending, setSessionActionPending] = useState<string | null>(null);
  const [sessionRefreshKey, setSessionRefreshKey] = useState(0);
  const [pendingUpdate, setPendingUpdate] = useState<{
    code: IdentityCode;
    message: string;
    data: {
      active?: boolean | null;
      visibilityScope?: "public" | "invited_by_you" | "invited_you" | "mutuals" | "disabled" | null;
      ttlSeconds?: number | null;
      confirmLastHandleDisable?: boolean | null;
    };
    isLastActiveHandle: boolean;
    stage: number;
  } | null>(null);
  const deviceSessions = useDeviceSessions(revealed, sessionRefreshKey);
  const { data: codes = [] } = useGetIdentityCodes({
    query: {
      queryKey: getGetIdentityCodesQueryKey(),
      refetchInterval: revealed ? 2000 : 10000,
      refetchOnWindowFocus: true,
    },
  });
  const sortedCodes = [...codes].sort((a, b) => `${a.kind}:${a.active ? "0" : "1"}:${a.code}:${a.createdAt}`.localeCompare(`${b.kind}:${b.active ? "0" : "1"}:${b.code}:${b.createdAt}`));
  const activeHandleCount = codes.filter((code) => code.kind === "alias" && code.active).length;

  const createCode = usePostIdentityCodes({
    mutation: {
      onSuccess: () => {
        setNewCode("");
        setError("");
        qc.invalidateQueries({ queryKey: getGetIdentityCodesQueryKey() });
      },
      onError: (err) => {
        const msg = err && typeof err === "object" && "response" in err
          ? ((err as { response?: { data?: { error?: string } } }).response?.data?.error ?? "Could not create code")
          : "Could not create code";
        setError(msg);
      },
    },
  });

  const updateCode = usePatchIdentityCodesCodeId({
    mutation: {
      onSuccess: () => {
        setError("");
        setPendingUpdate(null);
        qc.invalidateQueries({ queryKey: getGetIdentityCodesQueryKey() });
      },
      onError: () => setError("Could not update code"),
    },
  });

  const submitCode = async (e: React.FormEvent) => {
    e.preventDefault();
    const normalized = normalizeCodeInput(newCode);
    if (newKind === "alias" && normalized) rememberAssociatedHandle(normalized);
    createCode.mutate({
      data: {
        code: newKind === "alias" && normalized ? await hashIdentityCode(normalized) : normalized || null,
        kind: newKind,
        visibilityScope: "public",
        ttlSeconds: newTtl,
        maxUses: newKind === "invite" ? 1 : null,
      },
    });
  };

  const submitUnsealHandle = async (e: React.FormEvent) => {
    e.preventDefault();
    const token = getToken();
    const normalized = normalizeCodeInput(unsealHandle);
    if (!token) {
      setUnsealStatus({ tone: "error", text: "Sign in again before unsealing handles." });
      return;
    }
    if (!normalized) {
      setUnsealStatus({ tone: "error", text: "Enter a handle to unseal." });
      return;
    }

    setUnsealStatus(null);
    try {
      const hashed = await hashIdentityCode(normalized);
      const res = await fetch("/api/identity-codes/unseal", {
        method: "POST",
        headers: {
          "authorization": `Bearer ${token}`,
          "content-type": "application/json",
        },
        body: JSON.stringify({ code: hashed }),
      });
      const data = await res.json().catch(() => null) as (IdentityCode & { error?: string }) | null;
      if (!res.ok || !data?.id) {
        throw new Error(data?.error ?? "Could not unseal that handle.");
      }
      rememberUnsealedHandle(data.id, normalized);
      setUnsealedHandles(getUnsealedHandleLabels());
      setUnsealHandle("");
      setUnsealStatus({ tone: "ok", text: `${normalized} unsealed on this device.` });
    } catch (err) {
      setUnsealStatus({ tone: "error", text: err instanceof Error ? err.message : "Could not unseal that handle." });
    }
  };

  const addPasskey = async () => {
    if (passkeyPending) return;
    const token = getToken();
    if (!token) {
      setPasskeyStatus({ tone: "error", text: "Sign in again before adding a passkey." });
      return;
    }
    setPasskeyPending(true);
    setPasskeyStatus(null);
    setError("");
    try {
      await linkLocalPlatformPasskey(token);
      setPasskeyStatus({ tone: "ok", text: "New passkey saved for this account." });
    } catch (err) {
      setPasskeyStatus({
        tone: "error",
        text: err instanceof Error ? err.message : "Could not save a new passkey.",
      });
    } finally {
      setPasskeyPending(false);
    }
  };

  const expireSessions = async (body: { sessionId?: string; scope?: "all" | "others" }, pendingKey: string) => {
    if (sessionActionPending) return;
    const token = getToken();
    if (!token) {
      setSessionActionStatus({ tone: "error", text: "Sign in again before expiring sessions." });
      return;
    }

    const isAll = body.scope === "all";
    const isCurrent = !!body.sessionId && deviceSessions?.find((session) => session.id === body.sessionId)?.current;
    const confirmText = isAll
      ? "Expire all sessions, including this one? You will be logged out here too."
      : isCurrent
        ? "Expire this current session? You will be logged out."
        : body.scope === "others"
          ? "Expire every other active session?"
          : "Expire this session?";
    if (!window.confirm(confirmText)) return;

    setSessionActionPending(pendingKey);
    setSessionActionStatus(null);
    try {
      const res = await fetch("/api/auth/sessions/expire", {
        method: "POST",
        headers: {
          "authorization": `Bearer ${token}`,
          "content-type": "application/json",
        },
        body: JSON.stringify(body),
      });
      const data = await res.json().catch(() => null) as { ok?: boolean; expiredCurrent?: boolean; error?: string } | null;
      if (!res.ok) throw new Error(data?.error ?? "Could not expire session.");
      if (data?.expiredCurrent) {
        clearToken();
        setLocation("/login");
        return;
      }
      setSessionActionStatus({ tone: "ok", text: "Session expired." });
      setSessionRefreshKey((key) => key + 1);
    } catch (err) {
      setSessionActionStatus({ tone: "error", text: err instanceof Error ? err.message : "Could not expire session." });
    } finally {
      setSessionActionPending(null);
    }
  };

  const requestUpdate = (
    message: string,
    code: IdentityCode,
    data: {
      active?: boolean | null;
      visibilityScope?: "public" | "invited_by_you" | "invited_you" | "mutuals" | "disabled" | null;
      ttlSeconds?: number | null;
    }
  ) => {
    if (updateCode.isPending) return;
    const isLastActiveHandle = code.kind === "alias" && code.active && data.active === false && activeHandleCount <= 1;
    setPendingUpdate({ code, message, data, isLastActiveHandle, stage: isLastActiveHandle ? 1 : 0 });
  };

  const confirmPendingUpdate = async () => {
    if (!pendingUpdate || updateCode.isPending) return;
    if (pendingUpdate.isLastActiveHandle && pendingUpdate.stage < 3) {
      setPendingUpdate({ ...pendingUpdate, stage: pendingUpdate.stage + 1 });
      return;
    }
    let data = pendingUpdate.data;
    if (pendingUpdate.isLastActiveHandle) {
      try {
        const localHandle = getLastHandle();
        if (!localHandle) throw new Error("Enter your handle on the login screen before disabling your last handle.");
        const auth = await loginWithPasskey(localHandle);
        setToken(auth.token);
        setAuthHandle(auth.authHandle);
        data = { ...data, confirmLastHandleDisable: true };
      } catch (err: unknown) {
        setError(err instanceof Error ? err.message : "Fresh passkey verification failed.");
        return;
      }
    }
    updateCode.mutate({ codeId: pendingUpdate.code.id, data });
  };

  return (
    <div className="fixed inset-0 z-50 bg-background/80 backdrop-blur-sm flex items-center justify-center p-4">
      <div className="w-full max-w-2xl max-h-[90vh] overflow-y-auto border border-border bg-card">
        <div className="flex items-center justify-between p-4 border-b border-border/50">
          <div className="flex items-center gap-2">
            <Fingerprint className="w-4 h-4 text-primary" />
            <h2 className="font-mono font-bold text-sm tracking-widest">PROFILE / IDS</h2>
          </div>
          <button onClick={onClose} className="text-muted-foreground hover:text-foreground" data-testid="button-close-profile">
            <X className="w-4 h-4" />
          </button>
        </div>

        <div className="p-4 space-y-4">
          <div
            className="border border-border/50 bg-background/50 p-4"
            onPointerEnter={() => {
              if (!isMobile) setRevealed(true);
            }}
            onPointerLeave={() => {
              if (!isMobile) setRevealed(false);
            }}
            data-testid="button-hold-reveal-profile"
          >
            <div
              className="flex items-center gap-3"
              onClick={() => {
                if (isMobile) setRevealed((value) => !value);
              }}
            >
              <div className="w-9 h-9 rounded-full flex items-center justify-center text-white font-mono text-xs font-bold" style={{ backgroundColor: me.avatarColor ?? "#06b6d4" }}>
                {codename[0]}
              </div>
              <div className="min-w-0 flex-1">
                <div className="font-mono text-sm font-semibold">
                  {revealed ? (me.displayName ?? me.username) : codename}
                </div>
                <p className="font-mono text-xs text-muted-foreground mt-1">
                  {revealed
                    ? `${deviceSessions?.length ?? "..."} active login session${deviceSessions?.length === 1 ? "" : "s"}`
                    : isMobile
                      ? "Tap this row to reveal login sessions"
                      : "Hover this row to reveal login sessions"}
                </p>
              </div>
              <button
                type="button"
                disabled={passkeyPending}
                onClick={(e) => {
                  e.stopPropagation();
                  void addPasskey();
                }}
                className="shrink-0 border border-border bg-card/70 p-2 text-muted-foreground hover:border-primary/60 hover:text-primary disabled:opacity-50"
                aria-label="Create and save a new passkey"
                title="Create and save a new passkey"
                data-testid="button-add-settings-passkey"
              >
                <KeyRound className="w-4 h-4" />
              </button>
            </div>
            {passkeyStatus && (
              <p className={`mt-3 font-mono text-xs ${passkeyStatus.tone === "ok" ? "text-primary" : "text-destructive"}`}>
                {passkeyStatus.text}
              </p>
            )}
            {revealed && (
              <div className="mt-3 space-y-2">
                <div className="flex flex-col sm:flex-row gap-2">
                  <button
                    type="button"
                    disabled={!!sessionActionPending || !deviceSessions || deviceSessions.filter((session) => !session.current).length === 0}
                    onClick={(e) => {
                      e.stopPropagation();
                      void expireSessions({ scope: "others" }, "others");
                    }}
                    className="inline-flex items-center justify-center gap-2 border border-border bg-card/70 px-3 py-2 font-mono text-[10px] tracking-widest text-muted-foreground hover:border-destructive/50 hover:text-destructive disabled:opacity-50"
                    data-testid="button-expire-other-sessions"
                  >
                    <Trash2 className="w-3.5 h-3.5" />
                    {sessionActionPending === "others" ? "EXPIRING..." : "EXPIRE OTHERS"}
                  </button>
                  <button
                    type="button"
                    disabled={!!sessionActionPending || !deviceSessions || deviceSessions.length === 0}
                    onClick={(e) => {
                      e.stopPropagation();
                      void expireSessions({ scope: "all" }, "all");
                    }}
                    className="inline-flex items-center justify-center gap-2 border border-destructive/40 bg-destructive/10 px-3 py-2 font-mono text-[10px] tracking-widest text-destructive hover:bg-destructive/15 disabled:opacity-50"
                    data-testid="button-expire-all-sessions"
                  >
                    <Trash2 className="w-3.5 h-3.5" />
                    {sessionActionPending === "all" ? "EXPIRING..." : "EXPIRE ALL"}
                  </button>
                </div>
                {sessionActionStatus && (
                  <p className={`font-mono text-xs ${sessionActionStatus.tone === "ok" ? "text-primary" : "text-destructive"}`}>
                    {sessionActionStatus.text}
                  </p>
                )}
                {(deviceSessions ?? []).map((session, index) => (
                  <div key={session.id} className="border border-border/40 bg-card/60 px-3 py-2 font-mono text-[11px] text-muted-foreground">
                    <div className="flex items-center justify-between gap-2 text-foreground">
                      <span>{session.current ? "THIS DEVICE" : session.label.toUpperCase()}</span>
                      <div className="flex items-center gap-2">
                        <span>#{String(index + 1).padStart(2, "0")}</span>
                        <button
                          type="button"
                          disabled={!!sessionActionPending}
                          onClick={(e) => {
                            e.stopPropagation();
                            void expireSessions({ sessionId: session.id }, session.id);
                          }}
                          className="text-muted-foreground hover:text-destructive disabled:opacity-50"
                          aria-label={`Expire ${session.current ? "this session" : session.label}`}
                          title={`Expire ${session.current ? "this session" : session.label}`}
                          data-testid={`button-expire-session-${session.id}`}
                        >
                          <Trash2 className="w-3.5 h-3.5" />
                        </button>
                      </div>
                    </div>
                    <div className="mt-1">CREATED {formatSessionTime(session.createdAt)}</div>
                    <div>EXPIRES {formatSessionTime(session.expiresAt)}</div>
                  </div>
                ))}
                {deviceSessions && deviceSessions.length === 0 && (
                  <div className="font-mono text-xs text-muted-foreground">No active login sessions found.</div>
                )}
              </div>
            )}
          </div>

          <form onSubmit={submitCode} className="border border-border/50 bg-background/50 p-4 space-y-3">
            <div className="flex items-center gap-2">
              <KeyRound className="w-4 h-4 text-primary" />
              <h3 className="font-mono text-xs font-bold tracking-widest">CREATE HANDLE / INVITE CODE</h3>
            </div>
            <div className="grid grid-cols-1 md:grid-cols-[1fr_120px] gap-2">
              <input
                value={newCode}
                onChange={(e) => setNewCode(e.target.value)}
                className="bg-background border border-border px-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
                placeholder="@marlin or leave blank for random"
                autoCapitalize="none"
                data-testid="input-new-identity-code"
              />
              <select value={newKind} onChange={(e) => setNewKind(e.target.value as "alias" | "invite")} className="bg-background border border-border px-3 py-2 font-mono text-xs">
                <option value="alias">HANDLE - stable searchable ID</option>
                <option value="invite">INVITE - shareable expiring link code</option>
              </select>
            </div>
            <p className="font-mono text-xs text-muted-foreground leading-relaxed">{describeCodeKind(newKind)}</p>
            <div className="grid grid-cols-1 gap-2">
              <select value={newTtl} onChange={(e) => setNewTtl(Number(e.target.value))} className="bg-background border border-border px-3 py-2 font-mono text-xs">
                {CODE_TTL_OPTIONS.map((ttl) => <option key={ttl.value} value={ttl.value}>{ttl.label}</option>)}
              </select>
            </div>
            <p className="font-mono text-xs text-primary/80">New handles and invites are public when created. You can restrict or disable them after creation.</p>
            {error && <p className="font-mono text-xs text-destructive">{error}</p>}
            <button type="submit" disabled={createCode.isPending} className="w-full bg-primary text-primary-foreground font-mono text-xs tracking-widest py-2.5 disabled:opacity-50" data-testid="button-create-identity-code">
              {createCode.isPending ? "CREATING..." : "CREATE CODE"}
            </button>
          </form>

          <div className="space-y-2">
            <div className="font-mono text-xs text-muted-foreground tracking-widest">YOUR HANDLES / INVITES</div>
            <form onSubmit={submitUnsealHandle} className="border border-border/50 bg-background/50 p-3 space-y-2">
              <div className="font-mono text-xs text-primary tracking-widest">UNSEAL A HANDLE ON THIS DEVICE</div>
              <p className="font-mono text-xs text-muted-foreground leading-relaxed">
                Enter one of your handles to reveal its local label here. The server still stores only the sealed lookup.
              </p>
              <div className="grid grid-cols-1 sm:grid-cols-[1fr_auto] gap-2">
                <input
                  value={unsealHandle}
                  onChange={(e) => setUnsealHandle(e.target.value)}
                  className="bg-background border border-border px-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
                  placeholder="@stv"
                  autoCapitalize="none"
                  data-testid="input-unseal-handle"
                />
                <button
                  type="submit"
                  className="border border-primary/40 px-3 py-2 font-mono text-xs tracking-widest text-primary hover:bg-primary/10"
                  data-testid="button-unseal-handle"
                >
                  UNSEAL
                </button>
              </div>
              {unsealStatus && (
                <p className={`font-mono text-xs ${unsealStatus.tone === "ok" ? "text-primary" : "text-destructive"}`}>
                  {unsealStatus.text}
                </p>
              )}
            </form>
            {codes.length === 0 && (
              <div className="border border-border/50 bg-background/40 p-4 font-mono text-xs text-muted-foreground">No handles or invite codes yet.</div>
            )}
            {sortedCodes.map((code) => (
              <div key={code.id} className="border border-border/50 bg-background/40 p-3 space-y-3" data-testid={`identity-code-${code.id}`}>
                <div className="flex items-start justify-between gap-3">
                  <div>
                    <div className="font-mono text-sm font-semibold">{displayIdentityCode(code, unsealedHandles)}</div>
                    <div className="font-mono text-xs text-muted-foreground">
                      {code.active ? "ACTIVE" : "DISABLED"} / {code.visibilityScope.replaceAll("_", " ")} / {code.useCount}{code.maxUses ? ` of ${code.maxUses}` : ""} uses
                    </div>
                    <div className="font-mono text-xs text-muted-foreground mt-1">{formatExpiry(code.expiresAt)}</div>
                  </div>
                  <button
                    type="button"
                    disabled={updateCode.isPending}
                    onClick={() => requestUpdate(`${code.active ? "Disable" : "Enable"} ${displayIdentityCode(code, unsealedHandles)}? This changes whether people can discover it.`, code, { active: !code.active })}
                    className="border border-border px-3 py-1.5 font-mono text-xs hover:border-primary/50 disabled:opacity-50"
                  >
                    {code.active ? "DISABLE" : "ENABLE"}
                  </button>
                </div>
                <div className="grid grid-cols-1 md:grid-cols-3 gap-2">
                  <select
                    value={code.visibilityScope}
                    disabled={updateCode.isPending}
                    onChange={(e) => requestUpdate(`Change visibility for ${displayIdentityCode(code, unsealedHandles)} to ${e.target.value.replaceAll("_", " ")}?`, code, { visibilityScope: e.target.value as typeof code.visibilityScope })}
                    className="bg-background border border-border px-2 py-2 font-mono text-xs disabled:opacity-50"
                  >
                    {CODE_SCOPE_OPTIONS.map((scope) => <option key={scope.value} value={scope.value}>{scope.label}</option>)}
                  </select>
                  <select
                    defaultValue=""
                    disabled={updateCode.isPending}
                    onChange={(e) => {
                      if (e.target.value) {
                        const label = CODE_TTL_OPTIONS.find((ttl) => ttl.value === Number(e.target.value))?.label ?? e.target.value;
                        requestUpdate(`Change duration for ${displayIdentityCode(code, unsealedHandles)} to ${label}?`, code, { ttlSeconds: Number(e.target.value) });
                      }
                      e.currentTarget.value = "";
                    }}
                    className="bg-background border border-border px-2 py-2 font-mono text-xs disabled:opacity-50"
                  >
                    <option value="">RETIMING...</option>
                    {CODE_TTL_OPTIONS.map((ttl) => <option key={ttl.value} value={ttl.value}>{ttl.label}</option>)}
                  </select>
                  <button
                    type="button"
                    disabled={updateCode.isPending}
                    onClick={() => requestUpdate(`Roll/expire ${displayIdentityCode(code, unsealedHandles)}? This disables it immediately.`, code, { active: false, visibilityScope: "disabled" })}
                    className="border border-border px-2 py-2 font-mono text-xs hover:border-destructive/60 hover:text-destructive disabled:opacity-50"
                  >
                    ROLL / EXPIRE
                  </button>
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>
      {pendingUpdate && (
        <ConfirmCodeUpdateModal
          pendingUpdate={pendingUpdate}
          updatePending={updateCode.isPending}
          onCancel={() => setPendingUpdate(null)}
          onConfirm={() => void confirmPendingUpdate()}
        />
      )}
    </div>
  );
}

function ConfirmCodeUpdateModal({
  pendingUpdate,
  updatePending,
  onCancel,
  onConfirm,
}: {
  pendingUpdate: {
    code: IdentityCode;
    message: string;
    isLastActiveHandle: boolean;
    stage: number;
  };
  updatePending: boolean;
  onCancel: () => void;
  onConfirm: () => void;
}) {
  return (
    <div className="fixed inset-0 z-[60] bg-background/90 backdrop-blur-sm flex items-center justify-center p-4">
      <div className="w-full max-w-md border border-border bg-card p-5 shadow-2xl">
        <div className="flex items-center gap-2 mb-3">
          <Shield className={pendingUpdate.isLastActiveHandle ? "w-4 h-4 text-destructive" : "w-4 h-4 text-primary"} />
          <div className="font-mono text-xs tracking-widest text-muted-foreground">
            {pendingUpdate.isLastActiveHandle ? `LAST HANDLE CONFIRM ${pendingUpdate.stage}/3` : "CONFIRM CHANGE"}
          </div>
        </div>
        <h3 className="font-mono text-lg font-bold mb-2">
          {pendingUpdate.isLastActiveHandle ? "Disable your last active handle?" : "Apply this change?"}
        </h3>
        <p className="font-mono text-xs text-muted-foreground leading-relaxed">
          {pendingUpdate.isLastActiveHandle
            ? "This is your last active handle. If you disable it and then log out, you may not be able to recover this account. The final confirmation requires Face ID, Touch ID, Windows Hello, or your passkey provider."
            : pendingUpdate.message}
        </p>
        {pendingUpdate.isLastActiveHandle && (
          <p className="font-mono text-xs text-destructive mt-3">
            Step {pendingUpdate.stage} of 3: confirm you understand this can lock you out.
          </p>
        )}
        <div className="grid grid-cols-2 gap-2 mt-5">
          <button type="button" onClick={onCancel} className="border border-border px-3 py-2.5 font-mono text-xs hover:border-primary/50">
            CANCEL
          </button>
          <button
            type="button"
            disabled={updatePending}
            onClick={onConfirm}
            className="bg-destructive text-destructive-foreground px-3 py-2.5 font-mono text-xs disabled:opacity-50"
          >
            {pendingUpdate.isLastActiveHandle && pendingUpdate.stage === 3 ? "VERIFY PASSKEY" : "CONFIRM"}
          </button>
        </div>
      </div>
    </div>
  );
}

function RoomView({
  room,
  currentUserId,
  onBack,
  codenameForUser,
  roomCodename,
  onSensitiveRevealChange,
  online,
}: {
  room: Room;
  currentUserId: string;
  onBack: () => void;
  codenameForUser: (id: string) => string;
  roomCodename: string;
  onSensitiveRevealChange: (active: boolean) => void;
  online: boolean;
}) {
  const qc = useQueryClient();
  const [input, setInput] = useState("");
  const [heldPlaintext, setHeldPlaintext] = useState<{ id: string; text: string } | null>(null);
  const [revealError, setRevealError] = useState<{ id: string; text: string } | null>(null);
  const [hidden, setHidden] = useState(false);
  const [nowMs, setNowMs] = useState(() => Date.now());
  const [revealRoomName, setRevealRoomName] = useState(false);
  const [revealedSenderId, setRevealedSenderId] = useState<string | null>(null);
  const messagesScrollRef = useRef<HTMLDivElement>(null);
  const messagesEndRef = useRef<HTMLDivElement>(null);
  const shouldStickToBottomRef = useRef(true);
  const lastScrolledRoomRef = useRef(room.id);
  const revealTokenRef = useRef(0);
  const touchRevealActiveRef = useRef(false);
  const activeRevealRef = useRef<{ id: string; input: "mouse" | "touch"; released: boolean; painted: boolean } | null>(null);
  const revealFallbackTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);
  const mouseRevealHideTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);

  const { data: liveMessages = [] } = useGetRoomsRoomIdMessages(
    room.id,
    {},
    {
      query: {
        queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id),
        enabled: online,
        refetchInterval: 2500,
      },
    }
  );

  const { data: liveMembers = [] } = useGetRoomsRoomIdMembers(room.id, {
    query: { queryKey: getGetRoomsRoomIdMembersQueryKey(room.id), enabled: online },
  });
  const [offlineMessages, setOfflineMessages] = useState<Message[]>([]);
  const [offlineMembers, setOfflineMembers] = useState<NonNullable<Room["members"]>>([]);
  const [queuedMessages, setQueuedMessages] = useState<Message[]>([]);
  const [isSending, setIsSending] = useState(false);
  const [sendError, setSendError] = useState("");
  const roomQueuedMessages = useMemo(
    () => queuedMessages.filter((msg) => messageBelongsToRoom(msg, room.id)),
    [queuedMessages, room.id],
  );
  const queuedCount = roomQueuedMessages.filter((msg) => msg.localQueued).length;
  const visibleLiveMessages = (liveMessages as Message[]).map((live) => {
    const localFuzz = roomQueuedMessages.find((local) => (
      shouldKeepFuzzMetadata(local, room.deliveryFuzzSeconds, nowMs) && sameSentMessage(local, live)
    ));
    return localFuzz ? { ...live, createdAt: localFuzz.createdAt, localFuzzing: true } : live;
  });
  const visibleLocalMessages = roomQueuedMessages.filter((local) => {
    if (!local.localOptimistic && !local.localFuzzing) return true;
    return !visibleLiveMessages.some((live) => sameSentMessage(local, live));
  });
  const messages = online ? [...visibleLiveMessages, ...visibleLocalMessages] : offlineMessages.filter((msg) => messageBelongsToRoom(msg, room.id));
  const members = online ? liveMembers : offlineMembers;

  const postQueuedMessage = async (entry: OfflineOutboxEntry): Promise<Message> => {
    const senderDsaPublicKey = entry.senderDsaPublicKey ?? await senderDsaPublicKeyForSignedPayload({
      roomId: entry.roomId,
      senderId: currentUserId,
      ciphertext: entry.ciphertext,
      nonce: entry.nonce,
      algorithm: entry.algorithm,
      recipientEncryptedKeys: entry.recipientEncryptedKeys,
      signature: entry.signature,
    });
    const message = await postRoomsRoomIdMessages(entry.roomId, {
      ciphertext: entry.ciphertext,
      nonce: entry.nonce,
      algorithm: entry.algorithm,
      signature: entry.signature,
      senderDsaPublicKey,
      recipientEncryptedKeys: sendRecipientEncryptedKeys(entry.recipientEncryptedKeys),
      ttlSeconds: entry.ttlSeconds,
    }) as Message;
    await deleteOutboxEntry(entry.id);
    window.dispatchEvent(new Event("qs-offline-outbox-changed"));
    qc.invalidateQueries({ queryKey: getGetRoomsRoomIdMessagesQueryKey(entry.roomId) });
    qc.invalidateQueries({ queryKey: getGetRoomsQueryKey() });
    return message;
  };

  useEffect(() => {
    let cancelled = false;
    const load = async () => {
      const [cachedMessages, cachedMembers, outbox] = await Promise.all([
        getCachedRoomMessages(room.id),
        getCachedRoomMembers(room.id),
        getOutboxEntries(),
      ]);
      if (cancelled) return;
      const queued = outbox
        .filter((entry) => entry.roomId === room.id)
        .map((entry) => outboxEntryToMessage(entry, currentUserId));
      setQueuedMessages((current) => [
        ...queued,
        ...current.filter((message) => (
          messageBelongsToRoom(message, room.id) &&
          (message.localFuzzing || message.localOptimistic) &&
          !queued.some((queuedMessage) => queuedMessage.signature === message.signature)
        )),
      ]);
      setOfflineMessages([...cachedMessages, ...queued]);
      setOfflineMembers(cachedMembers);
    };
    void load();
    window.addEventListener("qs-offline-outbox-changed", load);
    return () => {
      cancelled = true;
      window.removeEventListener("qs-offline-outbox-changed", load);
    };
  }, [currentUserId, room.id]);

  useEffect(() => {
    if (!online || liveMessages.length === 0) return;
    let cancelled = false;
    const save = async () => {
      await cacheRoomMessages(room.id, liveMessages as Message[]);
      if (!cancelled) setOfflineMessages([...(liveMessages as Message[]), ...roomQueuedMessages]);
    };
    void save();
    return () => {
      cancelled = true;
    };
  }, [online, liveMessages, roomQueuedMessages, room.id]);

  useEffect(() => {
    if (!online || queuedMessages.length === 0) return;
    const fuzzSeconds = room.deliveryFuzzSeconds ?? 0;
    setQueuedMessages((current) => current.filter((local) => {
      if (!local.localOptimistic && !local.localFuzzing) return true;
      const hasLiveCopy = (liveMessages as Message[]).some((live) => sameSentMessage(local, live));
      if (hasLiveCopy) return shouldKeepFuzzMetadata(local, room.deliveryFuzzSeconds, nowMs);
      if (local.localOptimistic && !local.localFuzzing) return true;
      return shouldKeepFuzzMetadata(local, fuzzSeconds, nowMs);
    }));
  }, [liveMessages, nowMs, online, queuedMessages.length, room.deliveryFuzzSeconds]);

  useEffect(() => {
    if (!online || liveMembers.length === 0) return;
    void cacheRoomMembers(room.id, liveMembers);
    setOfflineMembers(liveMembers);
  }, [online, liveMembers, room.id]);

  useEffect(() => {
    const scrollEl = messagesScrollRef.current;
    if (!scrollEl) return;
    const roomChanged = lastScrolledRoomRef.current !== room.id;
    lastScrolledRoomRef.current = room.id;
    if (!roomChanged && !shouldStickToBottomRef.current) return;
    requestAnimationFrame(() => {
      scrollEl.scrollTop = scrollEl.scrollHeight;
      shouldStickToBottomRef.current = true;
    });
  }, [room.id, messages.length]);

  useEffect(() => {
    const purgeExpiredKeys = () => {
      const now = Date.now();
      setNowMs(now);
      for (const msg of messages as Message[]) {
        if (msg.expiresAt && new Date(msg.expiresAt).getTime() <= now) {
          if (heldPlaintext?.id === msg.id) forceHideRevealedMsg();
        }
      }
    };
    purgeExpiredKeys();
    const interval = setInterval(purgeExpiredKeys, 1000);
    return () => clearInterval(interval);
  }, [heldPlaintext?.id, messages]);

  useEffect(() => {
    if (!heldPlaintext?.id) return;
    const msg = (messages as Message[]).find((item) => item.id === heldPlaintext.id);
    if (!msg?.expiresAt) return;
    const delay = new Date(msg.expiresAt).getTime() - Date.now();
    if (delay <= 0) {
      forceHideRevealedMsg();
      return;
    }
    const timeout = setTimeout(forceHideRevealedMsg, delay);
    return () => clearTimeout(timeout);
  }, [heldPlaintext?.id, messages]);

  useEffect(() => {
    const onVis = () => {
      setHidden(document.visibilityState === "hidden");
      if (document.visibilityState === "hidden") forceHideRevealedMsg();
    };
    const onBlur = () => {
      setHidden(true);
      forceHideRevealedMsg();
    };
    const onFocus = () => setHidden(document.visibilityState === "hidden");
    document.addEventListener("visibilitychange", onVis);
    window.addEventListener("blur", onBlur);
    window.addEventListener("focus", onFocus);
    const block = (e: Event) => e.preventDefault();
    document.addEventListener("contextmenu", block);
    return () => {
      document.removeEventListener("visibilitychange", onVis);
      window.removeEventListener("blur", onBlur);
      window.removeEventListener("focus", onFocus);
      document.removeEventListener("contextmenu", block);
    };
  }, []);

  useEffect(() => {
    return () => onSensitiveRevealChange(false);
  }, [onSensitiveRevealChange]);

  const handleSend = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!input.trim() || isSending) return;
    const text = input;
    setInput("");
    setSendError("");
    setIsSending(true);
    let rawKey: Uint8Array | null = null;
    try {
      const canReachServer = online || await apiReachable();
      if (!canReachServer && room.memberCount > 1 && members.length < room.memberCount) {
        setSendError("This room's member list is not cached yet. Reconnect once before sending offline.");
        setInput(text);
        return;
      }

      const encrypted = await encryptMessage(text);
      const { ciphertext, nonce } = encrypted;
      const messageKey = encrypted.rawKey;
      rawKey = messageKey;
      const freshMembers = canReachServer ? await getRoomsRoomIdMembers(room.id).catch(() => members) : members;
      const recipientIds = Array.from(new Set([currentUserId, ...freshMembers.map((member) => member.id)]));
      const recipientEncryptedKeys: RecipientEncryptedKeys = {};
      await Promise.all(
        recipientIds.map(async (userId) => {
          const wrapped = userId === currentUserId
            ? await wrapMessageKeyForCurrentUserDevices(userId, messageKey)
            : await wrapMessageKeyForUserDevices(userId, messageKey);
          if (wrapped) recipientEncryptedKeys[userId] = wrapped;
        })
      );
      if (!recipientEncryptedKeys[currentUserId]) {
        setSendError("This device's local decrypt key is missing or out of sync. Rotate/link fresh keys before sending from here.");
        setInput(text);
        return;
      }
      if (recipientIds.some((userId) => !recipientEncryptedKeys[userId])) {
        setSendError("Could not encrypt for every current room member. Refresh the room and try again.");
        setInput(text);
        return;
      }
      const signature = await signMessagePayload({
        roomId: room.id,
        senderId: currentUserId,
        ciphertext,
        nonce,
        algorithm: CIPHER_SUITE,
        recipientEncryptedKeys,
      });
      if (!signature) {
        setSendError("This device does not have a local signing key. Use LINK FRESH KEYS, then try again.");
        setInput(text);
        return;
      }
      const sentAt = new Date().toISOString();

      const signedPayload = {
        roomId: room.id,
        senderId: currentUserId,
        ciphertext,
        nonce,
        algorithm: CIPHER_SUITE,
        recipientEncryptedKeys,
      };
      const payload = {
        ciphertext,
        nonce,
        algorithm: CIPHER_SUITE,
        signature,
        senderDsaPublicKey: await senderDsaPublicKeyForSignedPayload({ ...signedPayload, signature }) ?? getDsaPublicKey(),
        recipientEncryptedKeys,
        ttlSeconds: room.ttlSeconds,
      };
      const queued: OfflineOutboxEntry = {
        id: createLocalOutboxId(),
        roomId: room.id,
        ...payload,
        createdAt: sentAt,
        availableAt: sentAt,
      };
      await enqueueOutbox(queued);
      window.dispatchEvent(new Event("qs-offline-outbox-changed"));
      const queuedMessage = outboxEntryToMessage(queued, currentUserId);
      setQueuedMessages((current) => current.some((msg) => msg.id === queuedMessage.id) ? current : [...current, queuedMessage]);
      setOfflineMessages((current) => current.some((msg) => msg.id === queuedMessage.id) ? current : [...current, queuedMessage]);
      if (!canReachServer) {
        return;
      }

      const optimistic = localSentMessage({
        roomId: room.id,
        senderId: currentUserId,
        ciphertext,
        nonce,
        algorithm: CIPHER_SUITE,
        signature,
        recipientEncryptedKeys,
        createdAt: sentAt,
        localFuzzing: !!room.deliveryFuzzSeconds && room.deliveryFuzzSeconds > 0,
      });
      try {
        const sentMessage = await postQueuedMessage(queued);
        qc.setQueryData<Message[]>(getGetRoomsRoomIdMessagesQueryKey(room.id), (current = []) => {
          if (current.some((msg) => msg.id === sentMessage.id || (msg.signature && msg.signature === sentMessage.signature))) {
            return current;
          }
          return [...current, sentMessage];
        });
        setQueuedMessages((current) => [
          ...current.filter((msg) => msg.id !== queuedMessage.id && msg.signature !== queuedMessage.signature),
          optimistic,
        ]);
      } catch (err) {
        setSendError(`Server did not accept the message. It is still queued and will retry. ${errorMessage(err)}`);
        setQueuedMessages((current) => current.some((msg) => msg.id === queuedMessage.id) ? current : [...current, queuedMessage]);
      }
    } catch (err) {
      setSendError(err instanceof Error ? err.message : "Could not send message.");
      setInput(text);
    } finally {
      if (rawKey) clearBytes(rawKey);
      setIsSending(false);
    }
  };

  const revealMsg = async (msg: Message) => {
    const revealToken = ++revealTokenRef.current;
    const revealInput = activeRevealRef.current?.id === msg.id ? activeRevealRef.current.input : "mouse";
    if (msg.expiresAt && new Date(msg.expiresAt).getTime() <= Date.now()) {
      forceHideRevealedMsg();
      return;
    }
    setRevealError((current) => (current?.id === msg.id ? null : current));
    const verified = await verifyMessageSignature(room.id, msg);
    if (!verified) {
      const legacyMessage = isLegacySignatureGraceMessage(msg);
      if (msg.senderId !== currentUserId && !legacyMessage && revealToken === revealTokenRef.current) {
        setRevealError({
          id: msg.id,
          text: msg.signature ? "Message signature could not be verified." : "This message was not signed by a verified sender key.",
        });
      }
      if (msg.senderId !== currentUserId && !legacyMessage) return;
    }
    const k = msg.recipientEncryptedKeys?.[currentUserId]
      ? await unwrapMessageKeyForMe(msg.recipientEncryptedKeys[currentUserId])
      : null;
    if (!k) {
      if (revealToken === revealTokenRef.current) {
        setRevealError({
          id: msg.id,
          text: msg.recipientEncryptedKeys?.[currentUserId]
            ? "No local decrypt key on this device. Link from the device that created this account."
            : "This message was not encrypted for this device.",
        });
      }
      return;
    }
    try {
      const plaintext = await decryptMessage(msg.ciphertext, msg.nonce, k);
      if (revealToken !== revealTokenRef.current) return;
      if (msg.expiresAt && new Date(msg.expiresAt).getTime() <= Date.now()) {
        forceHideRevealedMsg();
        return;
      }
      if (activeRevealRef.current?.id === msg.id) {
        activeRevealRef.current.painted = true;
      }
      setHeldPlaintext({ id: msg.id, text: plaintext });
      if (activeRevealRef.current?.id === msg.id && activeRevealRef.current.released && revealInput === "touch") {
        if (revealFallbackTimerRef.current) clearTimeout(revealFallbackTimerRef.current);
        revealFallbackTimerRef.current = setTimeout(forceHideRevealedMsg, 900);
      }
    } catch {
      if (revealToken === revealTokenRef.current) {
        setRevealError({ id: msg.id, text: "This message was encrypted to an older local key that is not on this install." });
      }
    }
  };

  const hideRevealedMsg = () => {
    if (touchRevealActiveRef.current) return;
    if (activeRevealRef.current?.input === "mouse" && !activeRevealRef.current.released) return;
    hideRevealedMsgNow();
  };

  const forceHideRevealedMsg = () => {
    touchRevealActiveRef.current = false;
    activeRevealRef.current = null;
    clearEphemeralSecrets();
    hideRevealedMsgNow();
  };

  const hideRevealedMsgNow = () => {
    if (revealFallbackTimerRef.current) {
      clearTimeout(revealFallbackTimerRef.current);
      revealFallbackTimerRef.current = null;
    }
    if (mouseRevealHideTimerRef.current) {
      clearTimeout(mouseRevealHideTimerRef.current);
      mouseRevealHideTimerRef.current = null;
    }
    revealTokenRef.current += 1;
    setRevealedSenderId(null);
    onSensitiveRevealChange(false);
    setHeldPlaintext((current) => {
      if (!current) return null;
      return { id: current.id, text: "" };
    });
    queueMicrotask(() => setHeldPlaintext(null));
  };

  const startMessageReveal = (event: React.PointerEvent<HTMLButtonElement>, msg: Message) => {
    if (event.pointerType === "touch") return;
    startMouseMessageReveal(msg);
  };

  const startMouseMessageReveal = (msg: Message) => {
    if (mouseRevealHideTimerRef.current) {
      clearTimeout(mouseRevealHideTimerRef.current);
      mouseRevealHideTimerRef.current = null;
    }
    onSensitiveRevealChange(true);
    activeRevealRef.current = { id: msg.id, input: "mouse", released: false, painted: false };
    void revealMsg(msg);
  };

  const endMouseMessageReveal = () => {
    if (mouseRevealHideTimerRef.current) clearTimeout(mouseRevealHideTimerRef.current);
    const activeReveal = activeRevealRef.current;
    if (activeReveal?.input === "mouse") {
      activeReveal.released = true;
    }
    mouseRevealHideTimerRef.current = setTimeout(() => {
      if (activeRevealRef.current?.input === "mouse") activeRevealRef.current = null;
      clearEphemeralSecrets();
      hideRevealedMsg();
    }, 120);
  };

  const endPointerMessageReveal = (event: React.PointerEvent<HTMLButtonElement>) => {
    if (event.pointerType === "touch" || touchRevealActiveRef.current) return;
    if (event.type === "pointerup") return;
    clearEphemeralSecrets();
    hideRevealedMsg();
  };

  const startTouchMessageReveal = (event: React.TouchEvent<HTMLButtonElement>, msg: Message) => {
    event.preventDefault();
    event.stopPropagation();
    onSensitiveRevealChange(true);
    touchRevealActiveRef.current = true;
    activeRevealRef.current = { id: msg.id, input: "touch", released: false, painted: false };
    void revealMsg(msg);
  };

  const endTouchMessageReveal = (event: React.TouchEvent<HTMLButtonElement>) => {
    event.preventDefault();
    event.stopPropagation();
    const activeReveal = activeRevealRef.current;
    if (!activeReveal || activeReveal.input !== "touch") {
      forceHideRevealedMsg();
      return;
    }
    activeReveal.released = true;
    touchRevealActiveRef.current = false;
    clearEphemeralSecrets();
    if (activeReveal.painted) forceHideRevealedMsg();
  };

  const isExpired = (expiresAt?: string | null) => {
    if (!expiresAt) return false;
    return new Date(expiresAt).getTime() <= nowMs;
  };

  const handleMessagesScroll = () => {
    const scrollEl = messagesScrollRef.current;
    if (scrollEl) {
      shouldStickToBottomRef.current = scrollEl.scrollHeight - scrollEl.scrollTop - scrollEl.clientHeight < 96;
    }
    hideRevealedMsg();
  };

  return (
    <div className="flex flex-col h-full relative">
      <div className="flex items-center justify-between gap-2 px-4 md:px-6 py-3 md:py-4 border-b border-border/50 flex-shrink-0">
        <button
          onClick={onBack}
          className="md:hidden text-muted-foreground hover:text-foreground flex-shrink-0"
          aria-label="Back to channels"
          data-testid="button-back-to-channels"
        >
          <ArrowLeft className="w-5 h-5" />
        </button>
        <div className="flex-1 min-w-0">
          <div className="flex items-center gap-2">
            <h2 className="font-mono font-bold text-sm tracking-tight truncate">
              <button
                type="button"
                onPointerDown={() => setRevealRoomName(true)}
                onPointerEnter={(event) => {
                  if (event.pointerType === "mouse") setRevealRoomName(true);
                }}
                onPointerUp={() => setRevealRoomName(false)}
                onPointerCancel={() => setRevealRoomName(false)}
                onPointerLeave={() => setRevealRoomName(false)}
                className="truncate text-left hover:text-primary"
                data-testid="button-hold-reveal-room-name"
              >
                {revealRoomName ? getRoomLabel(room, currentUserId) : roomCodename}
              </button>
            </h2>
          </div>
          <ChatMetaRows room={room} revealed={revealRoomName} />
        </div>
        <div className="flex items-center gap-3 flex-shrink-0">
          <span className="font-mono text-xs text-muted-foreground flex items-center gap-1">
            <Users className="w-3 h-3" />
            {members.length}
          </span>
          {!online && (
            <span className="font-mono text-[10px] tracking-widest text-amber-500">OFFLINE</span>
          )}
          {queuedCount > 0 && (
            <span className="font-mono text-[10px] tracking-widest text-primary">{queuedCount} QUEUED</span>
          )}
        </div>
      </div>

      <div
        ref={messagesScrollRef}
        className="flex-1 overflow-y-auto p-4 space-y-3 select-none"
        style={{ filter: hidden ? "blur(24px)" : "none", WebkitUserSelect: "none", overscrollBehavior: "contain" }}
        onScroll={handleMessagesScroll}
      >
        {messages.length === 0 && (
          <div className="flex flex-col items-center justify-center h-full text-center">
            <Lock className="w-12 h-12 text-muted-foreground/30 mb-4" />
            <p className="font-mono text-sm text-muted-foreground">No messages yet</p>
            <p className="font-mono text-xs text-muted-foreground/60 mt-1">All messages are end-to-end encrypted</p>
          </div>
        )}

        {messages.map((msg) => {
          const isOwn = msg.senderId === currentUserId;
          const expired = isExpired(msg.expiresAt);
          const plaintext = heldPlaintext?.id === msg.id ? heldPlaintext.text : undefined;
          const error = revealError?.id === msg.id ? revealError.text : undefined;
          const senderLabel = revealedSenderId === msg.senderId ? (msg.senderUsername ?? codenameForUser(msg.senderId)) : codenameForUser(msg.senderId);
          const experimentalDecay = room.decayMode === "experimental_quorum_decay";
          const decayEvidence = experimentalDecay ? getDecayEvidence(msg as Message, nowMs) : null;
          const showGarbledPreview = !!decayEvidence?.active && !!plaintext;
          const blockRevealForDecay = showGarbledPreview && !!decayEvidence?.expired;
          const fuzzLabel = isOwn && msg.localFuzzing ? latestFuzzDeliveryLabel(msg.createdAt, room.deliveryFuzzSeconds, nowMs) : null;

          return (
            <div
              key={msg.id}
              className={`flex ${isOwn ? "justify-end" : "justify-start"}`}
              data-testid={`message-${msg.id}`}
              onMouseEnter={() => startMouseMessageReveal(msg as Message)}
              onMouseLeave={endMouseMessageReveal}
            >
              <div
                className={`max-w-[85%] md:max-w-[70%] ${isOwn ? "items-end" : "items-start"} flex flex-col gap-1`}
              >
                <div className="flex items-center gap-2">
                  {!isOwn && (
                    <button
                      type="button"
                      onPointerDown={() => setRevealedSenderId(msg.senderId)}
                      onPointerEnter={(event) => {
                        if (event.pointerType === "mouse") setRevealedSenderId(msg.senderId);
                      }}
                      onPointerUp={() => setRevealedSenderId(null)}
                      onPointerCancel={() => setRevealedSenderId(null)}
                      onPointerLeave={() => setRevealedSenderId(null)}
                      className="font-mono text-xs text-muted-foreground hover:text-primary"
                      data-testid={`button-hold-reveal-sender-${msg.id}`}
                    >
                      {senderLabel}
                    </button>
                  )}
                  {msg.localQueued && (
                    <span className="font-mono text-[10px] tracking-widest text-primary">QUEUED</span>
                  )}
                  {fuzzLabel && plaintext && (
                    <span className="font-mono text-[10px] tracking-widest text-amber-500">FUZZING</span>
                  )}
                  <MessageExpiry expiresAt={msg.expiresAt} revealed={!!plaintext} />
                </div>
                <div
                  className={`px-4 py-3 border ${
                    isOwn
                      ? "bg-primary/10 border-primary/30 text-foreground"
                      : "bg-card border-border/50 text-foreground"
                  }`}
                >
                  {expired && !experimentalDecay ? (
                    <p className="font-mono text-xs text-muted-foreground italic">
                      Message expired — cryptographically destroyed
                    </p>
                  ) : expired ? (
                    <p className="font-mono text-xs text-muted-foreground italic">
                      Message expired — cryptographic decay sealed
                    </p>
                  ) : blockRevealForDecay ? (
                    <div>
                      <p className="font-mono text-[10px] tracking-widest text-amber-500 mb-2">
                        {decayEvidence?.text} / QUORUM DECAY EVIDENCE
                      </p>
                      <p className="font-mono text-xs break-all text-muted-foreground" data-testid={`message-decay-preview-${msg.id}`}>
                        {deterministicGarbledPreview(msg as Message)}
                      </p>
                    </div>
                  ) : (
                    <button
                      type="button"
                      onPointerDown={(event) => startMessageReveal(event, msg as Message)}
                      onPointerUp={endPointerMessageReveal}
                      onTouchStart={(event) => startTouchMessageReveal(event, msg as Message)}
                      onTouchEnd={endTouchMessageReveal}
                      onTouchCancel={endTouchMessageReveal}
                      onTouchMove={(event) => event.preventDefault()}
                      onContextMenu={(event) => event.preventDefault()}
                      className="block w-full text-left select-none"
                      style={{ WebkitTouchCallout: "none", WebkitUserSelect: "none", touchAction: "none" }}
                      data-testid={`button-hold-reveal-${msg.id}`}
                    >
                      {plaintext ? (
                        <span>
                          <span className="block font-mono text-sm">{plaintext}</span>
                          {showGarbledPreview && (
                            <span className="mt-2 block">
                              <span className="block font-mono text-[10px] tracking-widest text-amber-500 mb-2">
                                {decayEvidence?.text} / QUORUM DECAY EVIDENCE
                              </span>
                              <span className="block font-mono text-xs break-all text-muted-foreground" data-testid={`message-decay-preview-${msg.id}`}>
                                {deterministicGarbledPreview(msg as Message)}
                              </span>
                            </span>
                          )}
                        </span>
                      ) : showGarbledPreview ? (
                        <span>
                          <span className="block font-mono text-[10px] tracking-widest text-amber-500 mb-2">
                            {decayEvidence?.text} / QUORUM DECAY EVIDENCE
                          </span>
                          <span className="block font-mono text-xs break-all text-muted-foreground hover:text-primary" data-testid={`message-decay-preview-${msg.id}`}>
                            {deterministicGarbledPreview(msg as Message)}
                          </span>
                        </span>
                      ) : (
                        <span className="flex items-center gap-2 font-mono text-xs text-muted-foreground hover:text-primary">
                          <Lock className="w-3 h-3" />
                          Encrypted — hover or hold to reveal
                        </span>
                      )}
                    </button>
                  )}
                  {error && (
                    <p className="mt-2 font-mono text-[10px] leading-snug text-destructive" data-testid={`message-reveal-error-${msg.id}`}>
                      {error}
                    </p>
                  )}
                  {msg.localQueued ? (
                    <p className="mt-2 font-mono text-[10px] leading-snug text-primary">
                      Encrypted on this device. It will be sent to the server when you are back online.
                    </p>
                  ) : fuzzLabel && plaintext ? (
                    <p className="mt-2 font-mono text-[10px] leading-snug text-amber-500">
                      Sent to server and being fuzzed. Recipient will receive it sometime in the next {fuzzLabel} at the latest.
                    </p>
                  ) : null}
                </div>
                <div className="flex items-center gap-2">
                  <span className="font-mono text-xs text-muted-foreground">
                    {plaintext ? formatTime(msg.createdAt) : "TIME SEALED"}
                  </span>
                  <Shield className="w-3 h-3 text-primary/50" />
                </div>
              </div>
            </div>
          );
        })}

        <div ref={messagesEndRef} />
      </div>

      <div className="border-t border-border/50 flex-shrink-0">
        {sendError && (
          <div className="border-b border-destructive/25 bg-destructive/10 px-4 py-2 font-mono text-[10px] text-destructive" data-testid="message-send-error">
            {sendError}
          </div>
        )}
        <form
          onSubmit={handleSend}
          className="flex items-center gap-2 px-4 py-4"
        >
          <input
            value={input}
            onChange={(e) => {
              setInput(e.target.value);
              if (sendError) setSendError("");
            }}
            className="flex-1 bg-background border border-border px-4 py-2.5 font-mono text-sm focus:outline-none focus:border-primary/60 transition-colors"
            placeholder="Type a message - will be encrypted client-side..."
            data-testid="input-message"
          />
          <button
            type="submit"
            disabled={isSending || !input.trim()}
            className="bg-primary text-primary-foreground p-2.5 hover:bg-primary/90 disabled:opacity-50 transition-all"
            data-testid="button-send"
          >
            <Send className="w-4 h-4" />
          </button>
        </form>
      </div>
    </div>
  );
}

export default function ChatApp() {
  const [, setLocation] = useLocation();
  const online = useOnlineStatus();
  const [activeRoomId, setActiveRoomId] = useState<string | null>(null);
  const [showNewRoom, setShowNewRoom] = useState(false);
  const [showProfile, setShowProfile] = useState(false);
  const [showVersionAudit, setShowVersionAudit] = useState(false);
  const [versionLabel, setVersionLabel] = useState(VERSION_LABEL_FALLBACK);
  const [versionToneValue, setVersionToneValue] = useState<VersionTone>("mismatch");
  const [privacyShield, setPrivacyShield] = useState<{ active: boolean; reason: string; error?: string }>({ active: false, reason: "" });
  const [captureWarning, setCaptureWarning] = useState<string | null>(null);
  const [privacyHandle, setPrivacyHandle] = useState(() => getLastHandle() ?? "");
  const [privacyNeedsHandle, setPrivacyNeedsHandle] = useState(() => !getLastHandle());
  const [isUnlockingPrivacy, setIsUnlockingPrivacy] = useState(false);
  const [cameraStatus, setCameraStatus] = useState<"scanning" | "clear" | "threat" | "unavailable">("scanning");
  const [cameraStatusDetail, setCameraStatusDetail] = useState("");
  const [pushStatus, setPushStatus] = useState<{ ok: boolean; reason: string } | null>(null);
  const [pushBusy, setPushBusy] = useState(false);
  const [keyRepairStatus, setKeyRepairStatus] = useState<{ ok: boolean; reason: string } | null>(null);
  const [keyRepairBusy, setKeyRepairBusy] = useState(false);
  const [revealedNameId, setRevealedNameId] = useState<string | null>(null);
  const videoRef = useRef<HTMLVideoElement>(null);
  const detectionIntervalRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const privacyAutoUnlockAttemptedRef = useRef(false);
  const revealNameTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);
  const autoKeyRepairAttemptedRef = useRef(false);
  const captureWarningTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);
  const activeRoomIdRef = useRef<string | null>(null);
  const sensitiveRevealActiveRef = useRef(false);
  const flashScanIntervalRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const flashCanvasRef = useRef<HTMLCanvasElement | null>(null);
  const flashBaselineRef = useRef<{ avg: number; brightRatio: number; peak: number } | null>(null);
  const flashStreakRef = useRef(0);
  const lastFlashDebugAtRef = useRef(0);
  const cameraStreamRef = useRef<MediaStream | null>(null);
  const startingCameraRef = useRef<Promise<void> | null>(null);
  const codenameFor = useMemo(() => createSessionCodenameFactory(), []);
  const qc = useQueryClient();

  const { data: liveMe, error: liveMeError } = useGetAuthMe({ query: { queryKey: getGetAuthMeQueryKey(), enabled: online } });
  const { data: liveRooms } = useGetRooms({ query: { queryKey: getGetRoomsQueryKey(), enabled: online, refetchInterval: () => randomRefetchInterval(28000, 97000) } });
  const uploadKeys = usePostKeysUpload();
  const [offlineMe, setOfflineMe] = useState<OfflineMe | null>(() => loadOfflineMe());
  const [offlineRooms, setOfflineRooms] = useState<Room[]>([]);
  const [outboxCount, setOutboxCount] = useState(0);
  const me = (online ? liveMe : offlineMe) ?? liveMe ?? offlineMe;
  const rooms = (online && liveRooms ? liveRooms : offlineRooms) as Room[];

  useEffect(() => {
    const status = typeof liveMeError === "object" && liveMeError && "status" in liveMeError
      ? Number((liveMeError as { status?: unknown }).status)
      : null;
    if (!online || status !== 401) return;
    clearToken();
    setPrivacyShield({ active: false, reason: "" });
    setLocation("/login");
  }, [liveMeError, online, setLocation]);

  const refreshSessionForKeyUpload = async (): Promise<void> => {
    const handle = normalizeCodeInput(getLastHandle() ?? privacyHandle ?? "");
    if (!handle) throw new Error("Fresh passkey verification is required before replacing this device key.");
    const auth = await loginWithPasskey(handle);
    setToken(auth.token);
    setAuthHandle(auth.authHandle);
    setLastHandle(handle);
  };

  const setSensitiveReveal = useCallback((active: boolean) => {
    sensitiveRevealActiveRef.current = active;
    if (!active) {
      flashBaselineRef.current = null;
      flashStreakRef.current = 0;
    }
  }, []);

  const enablePush = async () => {
    const token = getToken();
    if (!token || !online) return;
    setPushBusy(true);
    try {
      const result = await ensurePushSubscription(token);
      setPushStatus(result);
    } finally {
      setPushBusy(false);
    }
  };

  const relinkPushIfAllowed = async () => {
    const token = getToken();
    if (!token || !online) {
      if (!online) setPushStatus(null);
      return;
    }
    const permission = notificationPermission();
    if (permission === "granted") {
      if (await hasExistingPushSubscription()) {
        setPushStatus({ ok: true, reason: "subscribed" });
      }
      const result = await ensurePushSubscription(token);
      if (result.ok || !(await hasExistingPushSubscription())) {
        setPushStatus(result);
      }
      return;
    }
    setPushStatus({
      ok: false,
      reason: permission === "denied" ? "Notifications are blocked for this site." : "Tap enable to register this device for message alerts.",
    });
  };

  useEffect(() => {
    void relinkPushIfAllowed();
    const onFocus = () => void relinkPushIfAllowed();
    const onPageShow = () => void relinkPushIfAllowed();
    const onVisibility = () => {
      if (document.visibilityState === "visible") void relinkPushIfAllowed();
    };
    window.addEventListener("focus", onFocus);
    window.addEventListener("pageshow", onPageShow);
    document.addEventListener("visibilitychange", onVisibility);
    return () => {
      window.removeEventListener("focus", onFocus);
      window.removeEventListener("pageshow", onPageShow);
      document.removeEventListener("visibilitychange", onVisibility);
    };
  }, [online]);

  useEffect(() => {
    if (!liveMe) return;
    saveOfflineMe(liveMe);
    setOfflineMe(liveMe);
  }, [liveMe]);

  useEffect(() => {
    let cancelled = false;
    const load = async () => {
      const [cachedRooms, outbox] = await Promise.all([getCachedRooms(), getOutboxEntries()]);
      if (cancelled) return;
      setOfflineRooms(cachedRooms as Room[]);
      setOutboxCount(outbox.length);
    };
    void load();
    window.addEventListener("qs-offline-outbox-changed", load);
    return () => {
      cancelled = true;
      window.removeEventListener("qs-offline-outbox-changed", load);
    };
  }, []);

  useEffect(() => {
    if (!online || !liveRooms) return;
    void cacheRooms(liveRooms as Room[]);
    setOfflineRooms(liveRooms as Room[]);
  }, [online, liveRooms]);

  useEffect(() => {
    if (!online || !me?.id) return;
    let cancelled = false;
    const senderId = me.id;
    const flush = async () => {
      const entries = await getOutboxEntries();
      for (const entry of entries) {
        if (cancelled) return;
        try {
          const senderDsaPublicKey = entry.senderDsaPublicKey ?? await senderDsaPublicKeyForSignedPayload({
            roomId: entry.roomId,
            senderId,
            ciphertext: entry.ciphertext,
            nonce: entry.nonce,
            algorithm: entry.algorithm,
            recipientEncryptedKeys: entry.recipientEncryptedKeys,
            signature: entry.signature,
          });
          if (!senderDsaPublicKey) {
            console.warn("Queued message is missing a locally verifiable sender signing key.");
            continue;
          }
          await postRoomsRoomIdMessages(entry.roomId, {
            ciphertext: entry.ciphertext,
            nonce: entry.nonce,
            algorithm: entry.algorithm,
            signature: entry.signature,
            senderDsaPublicKey,
            recipientEncryptedKeys: sendRecipientEncryptedKeys(entry.recipientEncryptedKeys),
            ttlSeconds: entry.ttlSeconds,
          });
          await deleteOutboxEntry(entry.id);
          window.dispatchEvent(new Event("qs-offline-outbox-changed"));
          if (!cancelled) setOutboxCount((await getOutboxEntries()).length);
          qc.invalidateQueries({ queryKey: getGetRoomsRoomIdMessagesQueryKey(entry.roomId) });
          qc.invalidateQueries({ queryKey: getGetRoomsQueryKey() });
        } catch (err) {
          console.warn("Queued message flush failed", err);
          if (!cancelled) setOutboxCount((await getOutboxEntries()).length);
          continue;
        }
      }
      if (!cancelled) setOutboxCount((await getOutboxEntries()).length);
    };
    void flush();
    const onFocus = () => void flush();
    const onPageShow = () => void flush();
    const onVisibility = () => {
      if (document.visibilityState === "visible") void flush();
    };
    const interval = window.setInterval(() => void flush(), 30000);
    window.addEventListener("online", flush);
    window.addEventListener("focus", onFocus);
    window.addEventListener("pageshow", onPageShow);
    document.addEventListener("visibilitychange", onVisibility);
    return () => {
      cancelled = true;
      window.clearInterval(interval);
      window.removeEventListener("online", flush);
      window.removeEventListener("focus", onFocus);
      window.removeEventListener("pageshow", onPageShow);
      document.removeEventListener("visibilitychange", onVisibility);
    };
  }, [online, qc, me?.id]);

  const uploadLocalKeys = async () => {
    const keys = await getLocalKeyPairAsync();
    try {
      if (!keys.kemPublicKey || !keys.kemSecretKey || !keys.dsaPublicKey || !keys.dsaSecretKey) {
        setKeyRepairStatus({
          ok: false,
          reason: "Local private keys are missing on this install. Rotate this device to fresh keys for future messages, or use an install that still has the original keys for old messages.",
        });
        return false;
      }
      if (!localKemKeyPairCanRoundTrip(keys.kemPublicKey, keys.kemSecretKey)) {
        setKeyRepairStatus({
          ok: false,
          reason: "Local decrypt keys are out of sync on this install. Rotate this device to fresh keys before sending new messages from here.",
        });
        return false;
      }
      const kemSignature = ml_dsa87.sign(keys.kemPublicKey, keys.dsaSecretKey);
      const bundle = {
        kemPublicKey: bytesToBase64(keys.kemPublicKey),
        dsaPublicKey: bytesToBase64(keys.dsaPublicKey),
        kemSignature: bytesToBase64(kemSignature),
      };
      if (me?.dsaPublicKey && me.dsaPublicKey !== bundle.dsaPublicKey) {
        await refreshSessionForKeyUpload();
      }
      await uploadKeys.mutateAsync({
        data: bundle,
      });
      if (me?.id) await replaceTrustedKeyBundle(me.id, bundle);
      setKeyRepairStatus({ ok: true, reason: "Local key bundle relinked to this account." });
      return true;
    } finally {
      clearBytes(keys.kemSecretKey);
      clearBytes(keys.dsaSecretKey);
    }
  };

  const rotateLocalKeys = async () => {
    setKeyRepairBusy(true);
    let kemSecretKey: Uint8Array | null = null;
    let dsaSecretKey: Uint8Array | null = null;
    try {
      const kem = ml_kem1024.keygen();
      const dsa = ml_dsa87.keygen();
      kemSecretKey = kem.secretKey;
      dsaSecretKey = dsa.secretKey;
      const kemSignature = ml_dsa87.sign(kem.publicKey, dsa.secretKey);
      const bundle = {
        kemPublicKey: bytesToBase64(kem.publicKey),
        dsaPublicKey: bytesToBase64(dsa.publicKey),
        kemSignature: bytesToBase64(kemSignature),
      };
      if (me?.dsaPublicKey && me.dsaPublicKey !== bundle.dsaPublicKey) {
        await refreshSessionForKeyUpload();
      }
      await uploadKeys.mutateAsync({
        data: bundle,
      });
      storeKeyPair(kem.secretKey, kem.publicKey, dsa.secretKey, dsa.publicKey);
      if (me?.id) await replaceTrustedKeyBundle(me.id, bundle);
      setKeyRepairStatus({ ok: true, reason: "Fresh keys linked. New messages will encrypt to this install." });
    } catch (err) {
      setKeyRepairStatus({ ok: false, reason: err instanceof Error ? err.message : "Could not rotate keys for this install." });
    } finally {
      clearBytes(kemSecretKey);
      clearBytes(dsaSecretKey);
      setKeyRepairBusy(false);
    }
  };

  useEffect(() => {
    if (!me) return;
    const repairKeys = async () => {
      const keys = await getLocalKeyPairAsync();
      try {
        if (!keys.kemSecretKey || !keys.kemPublicKey || !keys.dsaSecretKey || !keys.dsaPublicKey) {
          autoKeyRepairAttemptedRef.current = true;
          setKeyRepairStatus({
            ok: false,
            reason: "Local private keys are missing on this install. Do not rotate yet if you need old messages here; use an install that still has the original keys, then relink or add this device.",
          });
          return;
        }
        if (!localKemKeyPairCanRoundTrip(keys.kemPublicKey, keys.kemSecretKey)) {
          autoKeyRepairAttemptedRef.current = true;
          setKeyRepairStatus({
            ok: false,
            reason: "Local decrypt keys are out of sync on this install. Rotate this device to fresh keys before sending new messages from here.",
          });
          return;
        }
        if (!sameBase64Bytes(me.kemPublicKey, keys.kemPublicKey) || !sameBase64Bytes(me.dsaPublicKey, keys.dsaPublicKey)) {
          await uploadLocalKeys();
        }
      } finally {
        clearBytes(keys.kemSecretKey);
        clearBytes(keys.dsaSecretKey);
      }
    };
    void repairKeys().catch((err) => {
        setKeyRepairStatus({ ok: false, reason: err instanceof Error ? err.message : "Could not relink local keys." });
    });
  }, [me?.id, me?.kemPublicKey, me?.dsaPublicKey]);

  const logout = usePostAuthLogout({
    mutation: {
      onSuccess: () => {
        clearToken();
        setLocation("/");
      },
    },
  });

  const activeRoom = rooms.find((r) => r.id === activeRoomId) as Room | undefined;
  useEffect(() => {
    let cancelled = false;
    fetch("/api/version", { cache: "no-store" })
      .then((res) => (res.ok ? res.json() as Promise<VersionAudit> : null))
      .then((audit) => {
        if (!cancelled && audit) {
          const label = audit.displayVersion || versionLabelFromIso(audit.publishTimeUtc);
          setVersionLabel(label);
          setVersionToneValue(versionStatus(audit));
        }
      })
      .catch(() => {
        if (!cancelled) {
          setVersionLabel(VERSION_LABEL_FALLBACK);
          setVersionToneValue("mismatch");
        }
      });
    return () => {
      cancelled = true;
    };
  }, []);

  useEffect(() => {
    activeRoomIdRef.current = activeRoomId;
  }, [activeRoomId]);

  const sendPrivacyAlert = async (roomId: string, label: string) => {
    const token = getToken();
    if (!token) return;
    await fetch(`/api/rooms/${roomId}/privacy-alert`, {
      method: "POST",
      headers: {
        Authorization: `Bearer ${token}`,
        "Content-Type": "application/json",
      },
      body: JSON.stringify({ reason: label }),
    }).catch(() => undefined);
  };

  const codenameForUser = (id: string) => codenameFor(`user:${id}`);
  const codenameForRoom = (id: string) => codenameFor(`room:${id}`);
  const scheduleNameReveal = (id: string) => {
    if (revealNameTimerRef.current) clearTimeout(revealNameTimerRef.current);
    revealNameTimerRef.current = setTimeout(() => setRevealedNameId(id), 220);
  };
  const clearNameReveal = () => {
    if (revealNameTimerRef.current) clearTimeout(revealNameTimerRef.current);
    revealNameTimerRef.current = null;
    setRevealedNameId(null);
  };
  const lockPrivacyShield = (reason: string) => {
    clearEphemeralSecrets();
    setPrivacyShield((current) => {
      if (!current.active) privacyAutoUnlockAttemptedRef.current = false;
      return { active: true, reason: current.active ? current.reason : reason };
    });
  };

  const warnCaptureAttempt = (reason: string) => {
    setCaptureWarning(reason);
    if (captureWarningTimerRef.current) clearTimeout(captureWarningTimerRef.current);
    captureWarningTimerRef.current = setTimeout(() => setCaptureWarning(null), CAPTURE_WARNING_MS);

    if ("Notification" in window && Notification.permission === "granted") {
      try {
        new Notification("QuantumShield privacy shield activated", {
          body: "A capture-related browser event was detected. Message content was hidden.",
          tag: "quantumshield-capture-warning",
          silent: true,
        });
      } catch {
        // Notification delivery is best-effort and varies across installed PWAs.
      }
    }
  };

  const lockForCaptureAttempt = (reason: string) => {
    lockPrivacyShield(reason);
    warnCaptureAttempt(reason);
  };

  const scanCameraFlash = (video: HTMLVideoElement): { triggered: boolean; candidate: boolean; detail: string; metrics?: Record<string, number | boolean | string> } => {
    const noFlash = { triggered: false, candidate: false, detail: "" };
    if (video.readyState < HTMLMediaElement.HAVE_CURRENT_DATA || video.videoWidth === 0 || video.videoHeight === 0) return noFlash;

    const canvas = flashCanvasRef.current ?? document.createElement("canvas");
    if (!flashCanvasRef.current) {
      canvas.width = FLASH_FRAME_WIDTH;
      canvas.height = FLASH_FRAME_HEIGHT;
      flashCanvasRef.current = canvas;
    }

    const ctx = canvas.getContext("2d", { willReadFrequently: true });
    if (!ctx) return noFlash;
    ctx.drawImage(video, 0, 0, FLASH_FRAME_WIDTH, FLASH_FRAME_HEIGHT);
    const data = ctx.getImageData(0, 0, FLASH_FRAME_WIDTH, FLASH_FRAME_HEIGHT).data;

    let luminanceTotal = 0;
    let brightPixels = 0;
    let veryBrightPixels = 0;
    let peak = 0;
    const pixelCount = FLASH_FRAME_WIDTH * FLASH_FRAME_HEIGHT;
    for (let i = 0; i < data.length; i += 4) {
      const lum = 0.2126 * data[i] + 0.7152 * data[i + 1] + 0.0722 * data[i + 2];
      luminanceTotal += lum;
      if (lum > 165) brightPixels += 1;
      if (lum > 205) veryBrightPixels += 1;
      if (lum > peak) peak = lum;
    }

    const avg = luminanceTotal / pixelCount;
    const brightRatio = brightPixels / pixelCount;
    const veryBrightRatio = veryBrightPixels / pixelCount;
    const baseline = flashBaselineRef.current ?? { avg, brightRatio, peak };
    const avgDelta = avg - baseline.avg;
    const brightDelta = brightRatio - baseline.brightRatio;
    const peakDelta = peak - baseline.peak;
    const globalFlash = avgDelta > 17 && brightDelta > 0.025 && avg > 42;
    const localizedFlash = peakDelta > 24 && brightDelta > 0.012 && veryBrightRatio > 0.004;
    const brightBloom = veryBrightRatio > 0.028 && brightDelta > 0.01 && avgDelta > 7;
    const dimPeakFlash = peakDelta > 42 && avgDelta > 0.35 && avg > 1 && brightDelta > -0.01;
    const dimPeakCandidate = peakDelta > 36 && avgDelta > 0.25 && avg > 1 && brightDelta > -0.01;
    const strongFlash = avgDelta > 34 || brightDelta > 0.075 || (peakDelta > 44 && veryBrightRatio > 0.01);
    const candidate = globalFlash || localizedFlash || brightBloom || dimPeakCandidate;
    flashStreakRef.current = candidate ? flashStreakRef.current + 1 : 0;
    const isFlash = strongFlash || dimPeakFlash || flashStreakRef.current >= 2;
    flashBaselineRef.current = candidate
      ? baseline
      : {
          avg: baseline.avg * 0.9 + avg * 0.1,
          brightRatio: baseline.brightRatio * 0.9 + brightRatio * 0.1,
          peak: baseline.peak * 0.86 + peak * 0.14,
        };
    if (isFlash) flashStreakRef.current = 0;
    return {
      triggered: isFlash,
      candidate,
      detail: `FLASH A+${avgDelta.toFixed(0)} B+${(brightDelta * 100).toFixed(1)} P+${peakDelta.toFixed(0)} V${(veryBrightRatio * 100).toFixed(1)}%`,
      metrics: {
        avg: Math.round(avg),
        avgDelta: Math.round(avgDelta),
        brightPct: Number((brightRatio * 100).toFixed(1)),
        brightDeltaPct: Number((brightDelta * 100).toFixed(1)),
        veryBrightPct: Number((veryBrightRatio * 100).toFixed(1)),
        peak: Math.round(peak),
        peakDelta: Math.round(peakDelta),
        candidate,
        strongFlash,
        dimPeakFlash,
        dimPeakCandidate,
        triggered: isFlash,
        streak: flashStreakRef.current,
        scanMs: FLASH_SCAN_MS,
      },
    };
  };

  const stopCamera = () => {
    if (detectionIntervalRef.current) {
      clearInterval(detectionIntervalRef.current);
      detectionIntervalRef.current = null;
    }
    if (flashScanIntervalRef.current) {
      clearInterval(flashScanIntervalRef.current);
      flashScanIntervalRef.current = null;
    }
    cameraStreamRef.current?.getTracks().forEach((track) => track.stop());
    cameraStreamRef.current = null;
    flashBaselineRef.current = null;
    flashStreakRef.current = 0;
    if (videoRef.current) videoRef.current.srcObject = null;
  };

  const isCameraRunning = () => {
    const stream = cameraStreamRef.current;
    return !!stream && stream.getVideoTracks().some((track) => track.readyState === "live" && track.enabled);
  };

  const sendFlashDebug = (roomId: string, flash: { detail: string; metrics?: Record<string, number | boolean | string> }) => {
    const token = getToken();
    if (!token) return;
    fetch(`/api/rooms/${roomId}/privacy-debug`, {
      method: "POST",
      headers: {
        Authorization: `Bearer ${token}`,
        "Content-Type": "application/json",
      },
      body: JSON.stringify({
        event: "flash-sample",
        detail: flash.detail,
        ...flash.metrics,
      }),
    }).catch(() => undefined);
  };

  const startCamera = async (force = false) => {
    if (!force && isCameraRunning()) return;
    if (startingCameraRef.current) return startingCameraRef.current;

    startingCameraRef.current = (async () => {
      stopCamera();
      setCameraStatus("scanning");
      setCameraStatusDetail("STARTING");

      try {
        const stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "user" }, audio: false });
        cameraStreamRef.current = stream;
        stream.getVideoTracks().forEach((track) => {
          const handleCameraLost = () => {
            lockPrivacyShield("Camera privacy scan stopped. Secure content is locked until camera access is restored.");
            setCameraStatus("unavailable");
            setCameraStatusDetail("CAMERA STOPPED");
          };
          track.addEventListener("ended", handleCameraLost, { once: true });
          track.addEventListener("mute", handleCameraLost, { once: true });
        });
        if (videoRef.current) {
          videoRef.current.srcObject = stream;
          await videoRef.current.play();
        }

        const detector = await getFrameThreatDetector();
        if (!detector) {
          setCameraStatus("unavailable");
          setCameraStatusDetail("MODEL UNAVAILABLE");
          return;
        }
        setCameraStatus("clear");
        setCameraStatusDetail("ON-DEVICE");

        flashScanIntervalRef.current = setInterval(() => {
          if (!videoRef.current) return;
          if (!sensitiveRevealActiveRef.current) {
            flashBaselineRef.current = null;
            flashStreakRef.current = 0;
            return;
          }
          const flash = scanCameraFlash(videoRef.current);
          const roomId = activeRoomIdRef.current;
          if (roomId && flash.metrics) {
            const now = Date.now();
            if (flash.triggered || now - lastFlashDebugAtRef.current > FLASH_DEBUG_SEND_MS) {
              lastFlashDebugAtRef.current = now;
              sendFlashDebug(roomId, flash);
            }
          }
          if (!flash.triggered) return;
          lockForCaptureAttempt("Possible screenshot flash reflected in the selfie camera. Secure content was hidden.");
          if (roomId) void sendPrivacyAlert(roomId, "possible screenshot flash");
          setCameraStatus("threat");
          setCameraStatusDetail(`FLASH GUARD / ${flash.detail}`);
        }, FLASH_SCAN_MS);

        detectionIntervalRef.current = setInterval(async () => {
          if (!videoRef.current) return;
          try {
            const threats = await detector.detect(videoRef.current);
            const strongest = threats.sort((a, b) => b.score - a.score)[0];
            setCameraStatus(strongest ? "threat" : "clear");
            if (strongest) {
              lockPrivacyShield(`Another device may be photographing this screen: ${strongest.label}.`);
              const roomId = activeRoomIdRef.current;
              if (roomId) void sendPrivacyAlert(roomId, strongest.label);
            }
            setCameraStatusDetail(
              strongest
                ? `${strongest.label.toUpperCase()} ${(strongest.score * 100).toFixed(0)}%`
                : "ON-DEVICE",
            );
          } catch {
            setCameraStatus("unavailable");
            setCameraStatusDetail("SCAN ERROR");
          }
        }, 2200);
      } catch {
        setCameraStatus("unavailable");
        setCameraStatusDetail("CAMERA DENIED");
      } finally {
        startingCameraRef.current = null;
      }
    })();

    return startingCameraRef.current;
  };

  const unlockPrivacyShield = async (source: "auto" | "manual" = "manual") => {
    setPrivacyShield((current) => ({ ...current, error: undefined }));
    setIsUnlockingPrivacy(true);
    let attemptedHandle = "";
    try {
      const handle = normalizeCodeInput(getLastHandle() || privacyHandle || "");
      attemptedHandle = handle;
      if (handle && online) {
        try {
          const data = await loginWithPasskey(handle);
          setToken(data.token);
          setAuthHandle(data.authHandle);
          setLastHandle(handle);
          setPrivacyHandle(handle);
          setPrivacyNeedsHandle(false);
        } catch {
          await verifyDevice();
          setPrivacyNeedsHandle(false);
        }
      } else {
        setPrivacyNeedsHandle(!handle && online);
        await verifyDevice();
      }
      if (!getToken()) {
        const keys = await getLocalKeyPairAsync();
        const hasLocalIdentity = !!keys.kemSecretKey && !!keys.dsaSecretKey && !!keys.kemPublicKey && !!keys.dsaPublicKey;
        clearBytes(keys.kemSecretKey);
        clearBytes(keys.dsaSecretKey);
        if (!hasLocalIdentity) throw new Error("No local offline identity keys are available on this device.");
      }
      await startCamera(true);
      if (!isCameraRunning()) {
        setPrivacyShield((current) => ({
          ...current,
          active: true,
          error: "Camera privacy scan is offline. Re-enable camera access before unlocking secure chat.",
        }));
        return;
      }
      setPrivacyShield({ active: false, reason: "" });
    } catch (err: unknown) {
      const message = err instanceof Error ? err.message : "Device verification failed.";
      const needsHandle = !attemptedHandle || message.toLowerCase().includes("handle");
      setPrivacyNeedsHandle(needsHandle);
      setPrivacyShield((current) => ({
        ...current,
        active: true,
        error: source === "auto" && attemptedHandle
          ? "Tap to unlock with your passkey and clear the privacy shield."
          : needsHandle
            ? "Enter your handle locally once, then unlock with your passkey."
            : message,
      }));
    } finally {
      setIsUnlockingPrivacy(false);
    }
  };

  useEffect(() => {
    if (!privacyShield.active || isUnlockingPrivacy || privacyAutoUnlockAttemptedRef.current) return;
    if (document.hidden || document.visibilityState !== "visible") return;
    const handle = normalizeCodeInput(getLastHandle() || privacyHandle || "");
    if (!handle) {
      setPrivacyNeedsHandle(true);
      return;
    }
    privacyAutoUnlockAttemptedRef.current = true;
    const id = window.setTimeout(() => void unlockPrivacyShield("auto"), 250);
    return () => window.clearTimeout(id);
  }, [privacyShield.active, privacyShield.reason, isUnlockingPrivacy, privacyHandle]);

  useEffect(() => {
    const shield = () => {
      if (isFreshLoginVerificationValid()) return;
      lockPrivacyShield("App was backgrounded or unfocused.");
    };
    const handleVisibility = () => {
      if (isFreshLoginVerificationValid()) return;
      if (document.hidden) lockPrivacyShield("App was backgrounded.");
    };
    const handleKeyDown = (event: KeyboardEvent) => {
      const key = event.key.toLowerCase();
      const isPrintScreen = key === "printscreen";
      const isMacScreenshotCombo = event.metaKey && event.shiftKey && ["3", "4", "5"].includes(key);
      if (isPrintScreen || isMacScreenshotCombo) {
        event.preventDefault();
        event.stopPropagation();
        lockForCaptureAttempt("Screenshot shortcut was detected. Secure content was hidden.");
      }
    };
    const handlePrint = (event: Event) => {
      event.preventDefault();
      lockForCaptureAttempt("Print or save-to-PDF was detected. Secure content was hidden.");
    };
    const handleCopy = (event: ClipboardEvent) => {
      event.preventDefault();
      lockForCaptureAttempt("Clipboard access was blocked. Secure content was hidden.");
    };
    const handlePageHide = () => {
      if (isFreshLoginVerificationValid()) return;
      lockPrivacyShield("App page was hidden by the browser.");
    };

    window.addEventListener("blur", shield);
    window.addEventListener("pagehide", handlePageHide);
    window.addEventListener("beforeprint", handlePrint);
    window.addEventListener("afterprint", handlePrint);
    window.addEventListener("keydown", handleKeyDown, { capture: true });
    window.addEventListener("keyup", handleKeyDown, { capture: true });
    document.addEventListener("copy", handleCopy);
    document.addEventListener("cut", handleCopy);
    document.addEventListener("visibilitychange", handleVisibility);

    return () => {
      if (captureWarningTimerRef.current) clearTimeout(captureWarningTimerRef.current);
      window.removeEventListener("blur", shield);
      window.removeEventListener("pagehide", handlePageHide);
      window.removeEventListener("beforeprint", handlePrint);
      window.removeEventListener("afterprint", handlePrint);
      window.removeEventListener("keydown", handleKeyDown, { capture: true });
      window.removeEventListener("keyup", handleKeyDown, { capture: true });
      document.removeEventListener("copy", handleCopy);
      document.removeEventListener("cut", handleCopy);
      document.removeEventListener("visibilitychange", handleVisibility);
    };
  }, []);

  useEffect(() => {
    void startCamera();
    return () => stopCamera();
  }, []);

  return (
    <div
      className="h-screen bg-background flex flex-col overflow-hidden select-none"
      onContextMenu={(event) => event.preventDefault()}
      data-testid="chat-privacy-surface"
    >
      <video ref={videoRef} className="absolute w-0 h-0 opacity-0 pointer-events-none" playsInline muted />
      <VersionAuditModal open={showVersionAudit} onClose={() => setShowVersionAudit(false)} />
      {privacyShield.active && (
        <div
          className="fixed inset-0 z-[100] bg-background flex flex-col items-center justify-center text-center px-6"
          onClick={(event) => {
            if (event.target === event.currentTarget && !isUnlockingPrivacy) void unlockPrivacyShield("manual");
          }}
        >
          <VersionBadge
            label={versionLabel}
            onClick={() => setShowVersionAudit(true)}
            className="absolute left-4 top-4"
            tone={versionToneValue}
          />
          <button
            type="button"
            onClick={() => {
              clearToken();
              clearEphemeralSecrets();
              setLocation("/");
            }}
            className="absolute right-4 top-4 border border-border px-4 py-2 font-mono text-[10px] tracking-widest text-muted-foreground hover:text-foreground hover:border-primary/40"
            data-testid="button-privacy-shield-logout"
          >
            LOG OUT / HOME
          </button>
          <Shield className="w-12 h-12 text-primary mb-4" />
          <p className="font-mono text-sm tracking-widest text-primary">PRIVACY SHIELD ACTIVE</p>
          <p className="font-mono text-xs text-muted-foreground mt-2 max-w-sm">
            {privacyShield.reason || "Secure content is locked until device verification succeeds."}
          </p>
          {privacyShield.error && (
            <p className="font-mono text-xs text-destructive mt-3 max-w-sm">{privacyShield.error}</p>
          )}
          {privacyNeedsHandle ? (
            <input
              value={privacyHandle}
              onChange={(event) => setPrivacyHandle(event.target.value)}
              className="mt-5 w-full max-w-xs bg-primary/5 border border-primary/60 ring-1 ring-primary/20 px-3 py-2.5 font-mono text-sm text-center focus:outline-none focus:border-primary focus:ring-primary/40"
              placeholder="@marlin"
              autoCapitalize="none"
              data-testid="input-privacy-shield-handle"
            />
          ) : (
            <p className="font-mono text-[11px] tracking-widest text-muted-foreground mt-5">USING SAVED PASSKEY HANDLE</p>
          )}
          <button
            type="button"
            onClick={() => void unlockPrivacyShield("manual")}
            disabled={isUnlockingPrivacy}
            className="mt-6 bg-primary text-primary-foreground font-mono text-xs tracking-widest px-6 py-3 hover:bg-primary/90 disabled:opacity-50"
            data-testid="button-unlock-privacy-shield"
          >
            {isUnlockingPrivacy ? "VERIFYING..." : "VERIFY PASSKEY"}
          </button>
        </div>
      )}
      <CameraScanStatus status={cameraStatus} detail={cameraStatusDetail} />
      {captureWarning && (
        <div className="border-b border-destructive/30 bg-destructive/10 px-4 py-2 flex items-start gap-2" data-testid="capture-warning">
          <CameraOff className="w-4 h-4 text-destructive mt-0.5 flex-shrink-0" />
          <div className="min-w-0">
            <p className="font-mono text-[10px] tracking-widest text-destructive">CAPTURE GUARD TRIGGERED</p>
            <p className="font-mono text-[10px] text-muted-foreground mt-0.5">{captureWarning}</p>
          </div>
        </div>
      )}
      {online && pushStatus && !pushStatus.ok && (
        <div className="border-b border-primary/20 bg-primary/5 px-4 py-2 flex flex-col sm:flex-row sm:items-center gap-2" data-testid="push-status-warning">
          <div className="flex-1 min-w-0">
            <p className="font-mono text-[10px] tracking-widest text-primary">PUSH NOTIFICATIONS OFFLINE</p>
            <p className="font-mono text-[10px] text-muted-foreground mt-0.5">{pushStatus.reason}</p>
          </div>
          <button
            type="button"
            onClick={() => void enablePush()}
            disabled={pushBusy}
            className="border border-primary/40 bg-primary/10 px-3 py-2 font-mono text-[10px] tracking-widest text-primary hover:bg-primary/15 disabled:opacity-50"
            data-testid="button-enable-push-inline"
          >
            {pushBusy ? "ENABLING..." : "ENABLE PUSH"}
          </button>
        </div>
      )}
      {!online && (
        <div className="border-b border-amber-500/30 bg-amber-500/10 px-4 py-2 flex items-start gap-2" data-testid="offline-vault-status">
          <Lock className="w-4 h-4 text-amber-500 mt-0.5 flex-shrink-0" />
          <div className="min-w-0">
            <p className="font-mono text-[10px] tracking-widest text-amber-500">OFFLINE VAULT</p>
            <p className="font-mono text-[10px] text-muted-foreground mt-0.5">
              Reading cached ciphertext only. New messages are encrypted on this device and queued until the server is reachable.
            </p>
          </div>
        </div>
      )}
      {outboxCount > 0 && (
        <div className="border-b border-primary/20 bg-primary/5 px-4 py-2" data-testid="offline-outbox-status">
          <p className="font-mono text-[10px] tracking-widest text-primary">{outboxCount} ENCRYPTED MESSAGE{outboxCount === 1 ? "" : "S"} QUEUED</p>
        </div>
      )}
      {keyRepairStatus && !keyRepairStatus.ok && (
        <div className="border-b border-destructive/25 bg-destructive/10 px-4 py-2 flex flex-col sm:flex-row sm:items-center gap-2" data-testid="key-status-warning">
          <div className="flex-1 min-w-0">
            <p className="font-mono text-[10px] tracking-widest text-destructive">LOCAL DECRYPT KEYS NOT LINKED</p>
            <p className="font-mono text-[10px] text-muted-foreground mt-0.5">{keyRepairStatus.reason}</p>
          </div>
          <button
            type="button"
            onClick={() => void rotateLocalKeys()}
            disabled={keyRepairBusy}
            className="border border-destructive/40 bg-destructive/10 px-3 py-2 font-mono text-[10px] tracking-widest text-destructive hover:bg-destructive/15 disabled:opacity-50"
            data-testid="button-rotate-local-keys"
          >
            {keyRepairBusy ? "LINKING..." : "LINK FRESH KEYS"}
          </button>
        </div>
      )}
      <div className="flex flex-1 min-h-0 overflow-hidden">
        <div
          className={`${
            activeRoomId ? "hidden md:flex" : "flex"
          } w-full md:w-72 border-r border-border/50 flex-col flex-shrink-0`}
        >
        <div className="flex items-center justify-between px-4 py-3 border-b border-border/50">
          <div className="flex items-center gap-2">
            <div className="w-6 h-6 bg-primary flex items-center justify-center">
              <Shield className="w-3.5 h-3.5 text-primary-foreground" />
            </div>
            <div className="flex flex-col leading-none">
              <span className="font-mono font-bold tracking-widest text-xs">QUANTUMSHIELD</span>
              <VersionBadge label={versionLabel} onClick={() => setShowVersionAudit(true)} className="mt-1 text-left" tone={versionToneValue} />
            </div>
          </div>
          <div className="flex items-center gap-1">
            <a
              href={GITHUB_URL}
              target="_blank"
              rel="noreferrer"
              className="inline-flex h-10 w-10 items-center justify-center border border-transparent text-muted-foreground hover:text-primary hover:border-primary/30 hover:bg-primary/5 transition-colors"
              title="View source on GitHub"
              data-testid="button-github"
            >
              <Github className="w-5 h-5" />
            </a>
            <button
              onClick={() => logout.mutate()}
              className="inline-flex h-10 w-10 items-center justify-center border border-transparent text-muted-foreground hover:text-foreground hover:border-border hover:bg-accent/30 transition-colors"
              title="Logout"
              data-testid="button-logout"
            >
              <LogOut className="w-5 h-5" />
            </button>
          </div>
        </div>

        {me && (
          <div className="px-4 py-3 border-b border-border/50">
            <div className="flex items-center gap-2">
              <div
                className="w-7 h-7 rounded-full flex items-center justify-center text-white text-xs font-bold font-mono"
                style={{ backgroundColor: me.avatarColor ?? "#06b6d4" }}
              >
                {codenameForUser(me.id)[0]}
              </div>
              <div className="flex-1 min-w-0">
                <button
                  type="button"
                  onPointerDown={() => scheduleNameReveal(`user:${me.id}`)}
                  onPointerUp={clearNameReveal}
                  onPointerCancel={clearNameReveal}
                  onPointerLeave={clearNameReveal}
                  className="block font-mono text-xs font-semibold text-left hover:text-primary"
                  data-testid="button-hold-reveal-account-name"
                >
                  {revealedNameId === `user:${me.id}` ? (me.displayName ?? me.username) : codenameForUser(me.id)}
                </button>
                <p className="font-mono text-xs text-muted-foreground">LOCAL DEVICE</p>
              </div>
              <button
                type="button"
                onClick={() => setShowProfile(true)}
                className="inline-flex h-10 w-10 items-center justify-center border border-transparent text-muted-foreground hover:text-primary hover:border-primary/30 hover:bg-primary/5 transition-colors"
                title="Manage profile, devices, handles, and invites"
                data-testid="button-profile-settings"
              >
                <Settings className="w-5 h-5" />
              </button>
            </div>
          </div>
        )}

        <div className="flex items-center justify-between px-4 py-2.5 border-b border-border/50">
          <span className="font-mono text-xs text-muted-foreground tracking-widest">CHANNELS</span>
          <button
            onClick={() => setShowNewRoom(true)}
            className="inline-flex h-11 w-11 items-center justify-center border border-primary/30 text-primary hover:bg-primary/10 transition-colors"
            title="New encrypted channel"
            data-testid="button-new-room"
          >
            <Plus className="w-5 h-5" />
          </button>
        </div>

        <div className="flex-1 overflow-y-auto">
          {rooms.length === 0 && (
            <div className="px-4 py-8 text-center">
              <MessageSquare className="w-8 h-8 text-muted-foreground/30 mx-auto mb-3" />
              <p className="font-mono text-xs text-muted-foreground">No channels yet</p>
              <button
                onClick={() => setShowNewRoom(true)}
                className="mt-3 font-mono text-xs text-primary hover:underline"
                data-testid="button-create-first-room"
              >
                Create one
              </button>
            </div>
          )}

          {rooms.map((room) => (
            <button
              key={room.id}
              onClick={() => setActiveRoomId(room.id)}
              onPointerDown={() => scheduleNameReveal(`room:${room.id}`)}
              onPointerEnter={(event) => {
                if (event.pointerType === "mouse") scheduleNameReveal(`room:${room.id}`);
              }}
              onPointerUp={clearNameReveal}
              onPointerCancel={clearNameReveal}
              onPointerLeave={clearNameReveal}
              className={`w-full px-4 py-3 flex items-center gap-3 border-b border-border/30 hover:bg-accent/30 transition-colors text-left ${
                activeRoomId === room.id ? "bg-accent/50 border-l-2 border-l-primary" : ""
              }`}
              data-testid={`button-room-${room.id}`}
            >
              <div
                className="w-8 h-8 rounded-full flex-shrink-0 flex items-center justify-center text-white text-xs font-bold font-mono"
                style={{
                  backgroundColor:
                    room.members?.find((m) => m.id !== me?.id)?.avatarColor ?? "#06b6d4",
                }}
              >
                {room.type === "group"
                  ? <Users className="w-4 h-4" />
                  : codenameForRoom(room.id)[0]}
              </div>
              <div className="flex-1 min-w-0">
                <div className="flex items-center justify-between">
                  <p className="font-mono text-xs font-semibold truncate">
                    {revealedNameId === `room:${room.id}` ? getRoomLabel(room as Room, me?.id) : codenameForRoom(room.id)}
                  </p>
                  {room.lastMessageAt && (
                    <span className="font-mono text-xs text-muted-foreground ml-2 flex-shrink-0">
                      {revealedNameId === `room:${room.id}` ? formatDate(room.lastMessageAt) : "SEALED"}
                    </span>
                  )}
                </div>
                <div className="flex items-center gap-1 mt-0.5 flex-wrap">
                  <Lock className="w-2.5 h-2.5 text-primary/50" />
                  <span className="font-mono text-xs text-muted-foreground">Encrypted</span>
                  {room.ttlSeconds && <TTLLabel seconds={room.ttlSeconds} mode={room.ttlMode} />}
                  {revealedNameId === `room:${room.id}` ? (
                    <>
                      <FuzzLabel seconds={room.deliveryFuzzSeconds} />
                      <DecayModeLabel mode={room.decayMode} />
                    </>
                  ) : (
                    <>
                      <span className="font-mono text-[10px] text-muted-foreground">DECAY SEALED</span>
                    </>
                  )}
                </div>
              </div>
            </button>
          ))}
        </div>
        </div>

        <div className={`${activeRoomId ? "flex" : "hidden md:flex"} flex-1 flex-col min-w-0`}>
        {activeRoom && me ? (
          <RoomView
            room={activeRoom as Room}
            currentUserId={me.id}
            onBack={() => setActiveRoomId(null)}
            codenameForUser={codenameForUser}
            roomCodename={codenameForRoom(activeRoom.id)}
            onSensitiveRevealChange={setSensitiveReveal}
            online={online}
          />
        ) : (
          <div className="flex-1 flex flex-col items-center justify-center text-center px-6">
            <div className="w-16 h-16 bg-primary/10 border border-primary/20 flex items-center justify-center mb-6">
              <Shield className="w-8 h-8 text-primary" />
            </div>
            <h2 className="font-mono font-bold text-xl tracking-tight mb-3">QuantumShield</h2>
            <VersionBadge label={versionLabel} onClick={() => setShowVersionAudit(true)} className="mb-4" tone={versionToneValue} />
            <p className="font-mono text-sm text-muted-foreground max-w-sm mb-2">
              Select a channel or create a new encrypted conversation
            </p>
            <p className="font-mono text-xs text-muted-foreground/60">
              {CIPHER_SUITE}
            </p>
            <button
              onClick={() => setShowNewRoom(true)}
              className="mt-8 flex items-center gap-2 bg-primary text-primary-foreground font-mono text-xs tracking-widest px-6 py-3 hover:bg-primary/90 transition-all"
              data-testid="button-new-channel"
            >
              <Plus className="w-4 h-4" />
              NEW ENCRYPTED CHANNEL
            </button>
          </div>
        )}
        </div>
      </div>

      {showNewRoom && me && (
        <NewRoomDialog
          onClose={() => setShowNewRoom(false)}
          currentUserId={me.id}
          codenameForUser={codenameForUser}
        />
      )}
      {showProfile && me && (
        <ProfilePanel
          onClose={() => setShowProfile(false)}
          me={me}
          codename={codenameForUser(me.id)}
        />
      )}
    </div>
  );
}
