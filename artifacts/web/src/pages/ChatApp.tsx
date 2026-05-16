import { useState, useEffect, useMemo, useRef } from "react";
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
} from "lucide-react";
import {
  useGetRooms,
  getGetRoomsQueryKey,
  usePostRooms,
  useGetAuthMe,
  usePostAuthLogout,
  useGetRoomsRoomIdMessages,
  getGetRoomsRoomIdMessagesQueryKey,
  usePostRoomsRoomIdMessages,
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
  type IdentityCode,
} from "@workspace/api-client-react";
import { useQueryClient } from "@tanstack/react-query";
import { clearToken, getKemSecretKey, getLastHandle, getToken, loginWithPasskey, setAuthHandle, setLastHandle, setToken, verifyDevice } from "@/lib/auth";
import { encryptMessage, importMessageKey, storeMessageKey, getMessageKey, decryptMessage, deleteMessageKey, CIPHER_SUITE } from "@/lib/crypto";
import { getFrameThreatDetector } from "@/lib/on-device-vision";
import { ml_kem1024 } from "@noble/post-quantum/ml-kem.js";
import { subscribeToPush } from "@/lib/pwa";

const GITHUB_URL = "https://github.com/stevemoraco/qs";

function normalizeCodeInput(value: string): string {
  return value.trim().replace(/^[@#]+/, "").toLowerCase();
}

function bytesToBase64(bytes: Uint8Array): string {
  let value = "";
  for (const byte of bytes) value += String.fromCharCode(byte);
  return btoa(value);
}

function base64ToBytes(value: string): Uint8Array {
  return Uint8Array.from(atob(value), (char) => char.charCodeAt(0));
}

async function aesGcmKeyFromBytes(bytes: Uint8Array): Promise<CryptoKey> {
  return crypto.subtle.importKey("raw", new Uint8Array(bytes).buffer as ArrayBuffer, { name: "AES-GCM", length: 256 }, false, ["encrypt", "decrypt"]);
}

async function wrapMessageKeyForUser(userId: string, rawMessageKey: Uint8Array): Promise<string | null> {
  try {
    const bundle = await getKeysUserId(userId);
    const { cipherText, sharedSecret } = ml_kem1024.encapsulate(base64ToBytes(bundle.kemPublicKey));
    const wrappingKey = await aesGcmKeyFromBytes(sharedSecret);
    const nonce = crypto.getRandomValues(new Uint8Array(12));
    const wrapped = await crypto.subtle.encrypt({ name: "AES-GCM", iv: nonce.buffer as ArrayBuffer }, wrappingKey, new Uint8Array(rawMessageKey).buffer as ArrayBuffer);
    return JSON.stringify({
      kemCiphertext: bytesToBase64(cipherText),
      nonce: bytesToBase64(nonce),
      wrappedKey: bytesToBase64(new Uint8Array(wrapped)),
    } satisfies WrappedMessageKey);
  } catch {
    return null;
  }
}

async function unwrapMessageKeyForMe(wrappedValue: string): Promise<CryptoKey | null> {
  const kemSecretKey = getKemSecretKey();
  if (!kemSecretKey) return null;
  try {
    const wrapped = JSON.parse(wrappedValue) as WrappedMessageKey;
    const sharedSecret = ml_kem1024.decapsulate(base64ToBytes(wrapped.kemCiphertext), kemSecretKey);
    const wrappingKey = await aesGcmKeyFromBytes(sharedSecret);
    const rawKey = await crypto.subtle.decrypt(
      { name: "AES-GCM", iv: base64ToBytes(wrapped.nonce).buffer as ArrayBuffer },
      wrappingKey,
      base64ToBytes(wrapped.wrappedKey).buffer as ArrayBuffer
    );
    return importMessageKey(new Uint8Array(rawKey));
  } catch {
    return null;
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
  members?: Array<{ id: string; username: string; displayName?: string | null; avatarColor?: string | null }> | null;
};

type Message = {
  id: string;
  senderId: string;
  senderUsername?: string | null;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys?: Record<string, string> | null;
  expiresAt?: string | null;
  createdAt: string;
  _plaintext?: string;
};

type WrappedMessageKey = {
  kemCiphertext: string;
  nonce: string;
  wrappedKey: string;
};

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
            QuantumShield uses your front camera locally to look for nearby recording devices pointed at the screen. Frames are processed on this device for privacy-shield decisions and are not uploaded or attached to messages.
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
  const [pendingTtlMode, setPendingTtlMode] = useState<"after_view" | "after_send" | null>(null);
  const [search, setSearch] = useState("");
  const [selectedIds, setSelectedIds] = useState<string[]>([]);
  const [revealedUserId, setRevealedUserId] = useState<string | null>(null);

  const normalizedSearch = normalizeCodeInput(search);
  const { data: searchResults } = useGetUsersSearch(
    { q: normalizedSearch },
    { query: { queryKey: getGetUsersSearchQueryKey({ q: normalizedSearch }), enabled: normalizedSearch.length > 0 } }
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
    ? "A handle is your reusable public name. People can search it, add you to chats, or link a device with it until you disable or expire it."
    : "An invite is a public one-use code. Share it with one person or device, and it stops working after it is used, expired, or rolled.";
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

function useDeviceCount(enabled: boolean) {
  const [count, setCount] = useState<number | null>(null);

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
        if (mounted && data && typeof data.activeDeviceCount === "number") {
          setCount(data.activeDeviceCount);
        }
      })
      .catch(() => {
        if (mounted) setCount(null);
      });
    return () => {
      mounted = false;
    };
  }, [enabled]);

  return count;
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
  const [revealed, setRevealed] = useState(false);
  const [newCode, setNewCode] = useState("");
  const [newKind, setNewKind] = useState<"alias" | "invite">("alias");
  const [newTtl, setNewTtl] = useState<number>(315360000);
  const [error, setError] = useState("");
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
  const deviceCount = useDeviceCount(revealed);
  const { data: codes = [] } = useGetIdentityCodes();
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

  const submitCode = (e: React.FormEvent) => {
    e.preventDefault();
    createCode.mutate({
      data: {
        code: normalizeCodeInput(newCode) || null,
        kind: newKind,
        visibilityScope: "public",
        ttlSeconds: newTtl,
        maxUses: newKind === "invite" ? 1 : null,
      },
    });
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
        const auth = await loginWithPasskey(pendingUpdate.code.code);
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
          <div className="border border-border/50 bg-background/50 p-4">
            <div className="flex items-center gap-3">
              <div className="w-9 h-9 rounded-full flex items-center justify-center text-white font-mono text-xs font-bold" style={{ backgroundColor: me.avatarColor ?? "#06b6d4" }}>
                {codename[0]}
              </div>
              <div className="min-w-0">
                <button
                  type="button"
                  onPointerDown={() => setRevealed(true)}
                  onPointerUp={() => setRevealed(false)}
                  onPointerCancel={() => setRevealed(false)}
                  onPointerLeave={() => setRevealed(false)}
                  className="font-mono text-sm font-semibold hover:text-primary"
                  data-testid="button-hold-reveal-profile"
                >
                  {revealed ? (me.displayName ?? me.username) : codename}
                </button>
                <p className="font-mono text-xs text-muted-foreground mt-1">
                  {revealed ? `${deviceCount ?? "..."} active linked device session${deviceCount === 1 ? "" : "s"}` : "Hold to reveal device links"}
                </p>
              </div>
            </div>
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
            {codes.length === 0 && (
              <div className="border border-border/50 bg-background/40 p-4 font-mono text-xs text-muted-foreground">No handles or invite codes yet.</div>
            )}
            {sortedCodes.map((code) => (
              <div key={code.id} className="border border-border/50 bg-background/40 p-3 space-y-3" data-testid={`identity-code-${code.id}`}>
                <div className="flex items-start justify-between gap-3">
                  <div>
                    <div className="font-mono text-sm font-semibold">{code.kind === "alias" ? "@" : "#"}{code.code}</div>
                    <div className="font-mono text-xs text-muted-foreground">
                      {code.active ? "ACTIVE" : "DISABLED"} / {code.visibilityScope.replaceAll("_", " ")} / {code.useCount}{code.maxUses ? ` of ${code.maxUses}` : ""} uses
                    </div>
                    <div className="font-mono text-xs text-muted-foreground mt-1">{formatExpiry(code.expiresAt)}</div>
                  </div>
                  <button
                    type="button"
                    disabled={updateCode.isPending}
                    onClick={() => requestUpdate(`${code.active ? "Disable" : "Enable"} ${code.code}? This changes whether people can discover or link with it.`, code, { active: !code.active })}
                    className="border border-border px-3 py-1.5 font-mono text-xs hover:border-primary/50 disabled:opacity-50"
                  >
                    {code.active ? "DISABLE" : "ENABLE"}
                  </button>
                </div>
                <div className="grid grid-cols-1 md:grid-cols-3 gap-2">
                  <select
                    value={code.visibilityScope}
                    disabled={updateCode.isPending}
                    onChange={(e) => requestUpdate(`Change visibility for ${code.code} to ${e.target.value.replaceAll("_", " ")}?`, code, { visibilityScope: e.target.value as typeof code.visibilityScope })}
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
                        requestUpdate(`Change duration for ${code.code} to ${label}?`, code, { ttlSeconds: Number(e.target.value) });
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
                    onClick={() => requestUpdate(`Roll/expire ${code.code}? This disables it immediately.`, code, { active: false, visibilityScope: "disabled" })}
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
          {pendingUpdate.isLastActiveHandle ? `Disable @${pendingUpdate.code.code}?` : "Apply this change?"}
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
}: {
  room: Room;
  currentUserId: string;
  onBack: () => void;
  codenameForUser: (id: string) => string;
  roomCodename: string;
}) {
  const qc = useQueryClient();
  const [input, setInput] = useState("");
  const [heldPlaintext, setHeldPlaintext] = useState<{ id: string; text: string } | null>(null);
  const [revealError, setRevealError] = useState<{ id: string; text: string } | null>(null);
  const [hidden, setHidden] = useState(false);
  const [revealRoomName, setRevealRoomName] = useState(false);
  const [revealedSenderId, setRevealedSenderId] = useState<string | null>(null);
  const messagesEndRef = useRef<HTMLDivElement>(null);
  const revealTokenRef = useRef(0);
  const touchRevealActiveRef = useRef(false);

  const { data: messages = [] } = useGetRoomsRoomIdMessages(
    room.id,
    {},
    {
      query: {
        queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id),
        refetchInterval: 3000,
      },
    }
  );

  const { data: members = [] } = useGetRoomsRoomIdMembers(room.id, {
    query: { queryKey: getGetRoomsRoomIdMembersQueryKey(room.id) },
  });

  const sendMessage = usePostRoomsRoomIdMessages({
    mutation: {
      onSuccess: () => {
        qc.invalidateQueries({ queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id) });
      },
    },
  });

  useEffect(() => {
    messagesEndRef.current?.scrollIntoView({ behavior: "smooth" });
  }, [messages]);

  useEffect(() => {
    const purgeExpiredKeys = () => {
      const now = Date.now();
      for (const msg of messages as Message[]) {
        if (msg.expiresAt && new Date(msg.expiresAt).getTime() <= now) {
          deleteMessageKey(msg.id);
          if (heldPlaintext?.id === msg.id) forceHideRevealedMsg();
        }
      }
    };
    purgeExpiredKeys();
    const interval = setInterval(purgeExpiredKeys, 1000);
    return () => clearInterval(interval);
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

  const handleSend = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!input.trim()) return;
    const text = input;
    setInput("");

    const { ciphertext, nonce, key, rawKey } = await encryptMessage(text);
    const freshMembers = await getRoomsRoomIdMembers(room.id).catch(() => members);
    const recipientIds = Array.from(new Set([currentUserId, ...freshMembers.map((member) => member.id)]));
    const recipientEncryptedKeys: Record<string, string> = {};
    await Promise.all(
      recipientIds.map(async (userId) => {
        const wrapped = await wrapMessageKeyForUser(userId, rawKey);
        if (wrapped) recipientEncryptedKeys[userId] = wrapped;
      })
    );

    sendMessage.mutate(
      {
        roomId: room.id,
        data: {
          ciphertext,
          nonce,
          algorithm: CIPHER_SUITE,
          recipientEncryptedKeys,
          ttlSeconds: room.ttlSeconds,
        },
      },
      {
        onSuccess: (msg) => {
          storeMessageKey(msg.id, key);
        },
      }
    );
  };

  const revealMsg = async (msg: Message, key?: CryptoKey) => {
    const revealToken = ++revealTokenRef.current;
    setRevealError((current) => (current?.id === msg.id ? null : current));
    let k = key ?? getMessageKey(msg.id);
    if (!k && msg.recipientEncryptedKeys?.[currentUserId]) {
      k = (await unwrapMessageKeyForMe(msg.recipientEncryptedKeys[currentUserId])) ?? undefined;
      if (k) storeMessageKey(msg.id, k);
    }
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
      setHeldPlaintext({ id: msg.id, text: plaintext });
    } catch {
      if (revealToken === revealTokenRef.current) {
        setRevealError({ id: msg.id, text: "Could not decrypt this message on this device." });
      }
    }
  };

  const hideRevealedMsg = () => {
    if (touchRevealActiveRef.current) return;
    hideRevealedMsgNow();
  };

  const forceHideRevealedMsg = () => {
    touchRevealActiveRef.current = false;
    hideRevealedMsgNow();
  };

  const hideRevealedMsgNow = () => {
    revealTokenRef.current += 1;
    setRevealedSenderId(null);
    setHeldPlaintext((current) => {
      if (!current) return null;
      return { id: current.id, text: "" };
    });
    queueMicrotask(() => setHeldPlaintext(null));
  };

  const startMessageReveal = (event: React.PointerEvent<HTMLButtonElement>, msg: Message) => {
    if (event.pointerType === "touch") return;
    event.currentTarget.setPointerCapture?.(event.pointerId);
    void revealMsg(msg);
  };

  const endPointerMessageReveal = (event: React.PointerEvent<HTMLButtonElement>) => {
    if (event.pointerType === "touch" || touchRevealActiveRef.current) return;
    hideRevealedMsg();
  };

  const startTouchMessageReveal = (event: React.TouchEvent<HTMLButtonElement>, msg: Message) => {
    event.preventDefault();
    event.stopPropagation();
    touchRevealActiveRef.current = true;
    void revealMsg(msg);
  };

  const endTouchMessageReveal = (event: React.TouchEvent<HTMLButtonElement>) => {
    event.preventDefault();
    event.stopPropagation();
    forceHideRevealedMsg();
  };

  const isExpired = (expiresAt?: string | null) => {
    if (!expiresAt) return false;
    return new Date(expiresAt).getTime() < Date.now();
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
                onPointerUp={() => setRevealRoomName(false)}
                onPointerCancel={() => setRevealRoomName(false)}
                onPointerLeave={() => setRevealRoomName(false)}
                className="truncate text-left hover:text-primary"
                data-testid="button-hold-reveal-room-name"
              >
                {revealRoomName ? getRoomLabel(room, currentUserId) : roomCodename}
              </button>
            </h2>
            <TTLLabel seconds={room.ttlSeconds} mode={room.ttlMode} />
          </div>
          <div className="flex items-center gap-2 mt-1 min-w-0">
            <Shield className="w-3 h-3 text-primary flex-shrink-0" />
            <span className="font-mono text-[10px] md:text-xs text-primary truncate">{CIPHER_SUITE}</span>
          </div>
        </div>
        <div className="flex items-center gap-3 flex-shrink-0">
          <span className="font-mono text-xs text-muted-foreground flex items-center gap-1">
            <Users className="w-3 h-3" />
            {members.length}
          </span>
        </div>
      </div>

      <div
        className="flex-1 overflow-y-auto p-4 space-y-3 select-none"
        style={{ filter: hidden ? "blur(24px)" : "none", WebkitUserSelect: "none", overscrollBehavior: "contain" }}
        onScroll={hideRevealedMsg}
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

          return (
            <div
              key={msg.id}
              className={`flex ${isOwn ? "justify-end" : "justify-start"}`}
              data-testid={`message-${msg.id}`}
            >
              <div className={`max-w-[85%] md:max-w-[70%] ${isOwn ? "items-end" : "items-start"} flex flex-col gap-1`}>
                <div className="flex items-center gap-2">
                  {!isOwn && (
                    <button
                      type="button"
                      onPointerDown={() => setRevealedSenderId(msg.senderId)}
                      onPointerUp={() => setRevealedSenderId(null)}
                      onPointerCancel={() => setRevealedSenderId(null)}
                      onPointerLeave={() => setRevealedSenderId(null)}
                      className="font-mono text-xs text-muted-foreground hover:text-primary"
                      data-testid={`button-hold-reveal-sender-${msg.id}`}
                    >
                      {senderLabel}
                    </button>
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
                  {expired ? (
                    <p className="font-mono text-xs text-muted-foreground italic">
                      Message expired — cryptographically destroyed
                    </p>
                  ) : (
                    <button
                      type="button"
                      onPointerDown={(event) => startMessageReveal(event, msg as Message)}
                      onPointerUp={endPointerMessageReveal}
                      onPointerCancel={endPointerMessageReveal}
                      onPointerLeave={endPointerMessageReveal}
                      onLostPointerCapture={endPointerMessageReveal}
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
                        <span className="font-mono text-sm">{plaintext}</span>
                      ) : (
                        <span className="flex items-center gap-2 font-mono text-xs text-muted-foreground hover:text-primary">
                          <Lock className="w-3 h-3" />
                          Encrypted — hold to reveal
                        </span>
                      )}
                    </button>
                  )}
                  {error && (
                    <p className="mt-2 font-mono text-[10px] leading-snug text-destructive" data-testid={`message-reveal-error-${msg.id}`}>
                      {error}
                    </p>
                  )}
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

      <form
        onSubmit={handleSend}
        className="flex items-center gap-2 px-4 py-4 border-t border-border/50 flex-shrink-0"
      >
        <input
          value={input}
          onChange={(e) => setInput(e.target.value)}
          className="flex-1 bg-background border border-border px-4 py-2.5 font-mono text-sm focus:outline-none focus:border-primary/60 transition-colors"
          placeholder="Type a message — will be encrypted client-side..."
          data-testid="input-message"
        />
        <button
          type="submit"
          disabled={sendMessage.isPending || !input.trim()}
          className="bg-primary text-primary-foreground p-2.5 hover:bg-primary/90 disabled:opacity-50 transition-all"
          data-testid="button-send"
        >
          <Send className="w-4 h-4" />
        </button>
      </form>
    </div>
  );
}

export default function ChatApp() {
  const [, setLocation] = useLocation();
  const [activeRoomId, setActiveRoomId] = useState<string | null>(null);
  const [showNewRoom, setShowNewRoom] = useState(false);
  const [showProfile, setShowProfile] = useState(false);
  const [privacyShield, setPrivacyShield] = useState<{ active: boolean; reason: string; error?: string }>({ active: false, reason: "" });
  const [privacyHandle, setPrivacyHandle] = useState(() => getLastHandle() ?? "");
  const [privacyNeedsHandle, setPrivacyNeedsHandle] = useState(() => !getLastHandle());
  const [isUnlockingPrivacy, setIsUnlockingPrivacy] = useState(false);
  const [cameraStatus, setCameraStatus] = useState<"scanning" | "clear" | "threat" | "unavailable">("scanning");
  const [cameraStatusDetail, setCameraStatusDetail] = useState("");
  const [revealedNameId, setRevealedNameId] = useState<string | null>(null);
  const videoRef = useRef<HTMLVideoElement>(null);
  const detectionIntervalRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const privacyAutoUnlockAttemptedRef = useRef(false);
  const revealNameTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);
  const codenameFor = useMemo(() => createSessionCodenameFactory(), []);
  const qc = useQueryClient();

  const { data: me } = useGetAuthMe();
  const { data: rooms = [] } = useGetRooms({ query: { queryKey: getGetRoomsQueryKey(), refetchInterval: 5000 } });

  useEffect(() => {
    const token = getToken();
    if (token) void subscribeToPush(token);
  }, []);

  const logout = usePostAuthLogout({
    mutation: {
      onSuccess: () => {
        clearToken();
        setLocation("/");
      },
    },
  });

  const activeRoom = rooms.find((r) => r.id === activeRoomId) as Room | undefined;
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
    setPrivacyShield((current) => {
      if (!current.active) privacyAutoUnlockAttemptedRef.current = false;
      return { active: true, reason: current.active ? current.reason : reason };
    });
  };

  const unlockPrivacyShield = async (source: "auto" | "manual" = "manual") => {
    setPrivacyShield((current) => ({ ...current, error: undefined }));
    setIsUnlockingPrivacy(true);
    let attemptedHandle = "";
    try {
      const handle = normalizeCodeInput(getLastHandle() || privacyHandle || "");
      attemptedHandle = handle;
      if (handle) {
        const data = await loginWithPasskey(handle);
        setToken(data.token);
        setAuthHandle(data.authHandle);
        setLastHandle(handle);
        setPrivacyHandle(handle);
        setPrivacyNeedsHandle(false);
      } else {
        setPrivacyNeedsHandle(true);
        await verifyDevice();
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
          ? "Tap to verify your passkey and clear the privacy shield."
          : needsHandle
            ? "Enter your handle once and verify with your passkey to unlock."
            : message,
      }));
    } finally {
      setIsUnlockingPrivacy(false);
    }
  };

  useEffect(() => {
    if (!privacyShield.active || isUnlockingPrivacy || privacyAutoUnlockAttemptedRef.current) return;
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
    const shield = () => lockPrivacyShield("App was backgrounded or unfocused.");
    const handleVisibility = () => {
      if (document.hidden) lockPrivacyShield("App was backgrounded.");
    };
    const handleKeyDown = (event: KeyboardEvent) => {
      if (event.key === "PrintScreen") {
        lockPrivacyShield("Screenshot key was detected.");
      }
    };

    window.addEventListener("blur", shield);
    window.addEventListener("beforeprint", shield);
    window.addEventListener("keydown", handleKeyDown);
    document.addEventListener("visibilitychange", handleVisibility);

    return () => {
      window.removeEventListener("blur", shield);
      window.removeEventListener("beforeprint", shield);
      window.removeEventListener("keydown", handleKeyDown);
      document.removeEventListener("visibilitychange", handleVisibility);
    };
  }, []);

  useEffect(() => {
    let stream: MediaStream | null = null;
    let mounted = true;

    const startCamera = async () => {
      try {
        stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "user" }, audio: false });
        if (!mounted) return;
        if (videoRef.current) {
          videoRef.current.srcObject = stream;
          await videoRef.current.play();
        }

        const detector = await getFrameThreatDetector();
        if (!mounted) return;
        if (!detector) {
          setCameraStatus("unavailable");
          setCameraStatusDetail("MODEL UNAVAILABLE");
          return;
        }
        setCameraStatus("clear");
        setCameraStatusDetail("ON-DEVICE");

        detectionIntervalRef.current = setInterval(async () => {
          if (!videoRef.current) return;
          try {
            const threats = await detector.detect(videoRef.current);
            const strongest = threats.sort((a, b) => b.score - a.score)[0];
            setCameraStatus(strongest ? "threat" : "clear");
            if (strongest) lockPrivacyShield(`Recording device detected: ${strongest.label}.`);
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
      }
    };

    startCamera();

    return () => {
      mounted = false;
      if (detectionIntervalRef.current) clearInterval(detectionIntervalRef.current);
      if (stream) stream.getTracks().forEach((t) => t.stop());
    };
  }, []);

  return (
    <div
      className="h-screen bg-background flex flex-col overflow-hidden select-none"
      onContextMenu={(event) => event.preventDefault()}
      data-testid="chat-privacy-surface"
    >
      <video ref={videoRef} className="absolute w-0 h-0 opacity-0 pointer-events-none" playsInline muted />
      {privacyShield.active && (
        <div
          className="fixed inset-0 z-[100] bg-background flex flex-col items-center justify-center text-center px-6"
          onClick={(event) => {
            if (event.target === event.currentTarget && !isUnlockingPrivacy) void unlockPrivacyShield("manual");
          }}
        >
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
            <span className="font-mono font-bold tracking-widest text-xs">QUANTUMSHIELD</span>
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
                <div className="flex items-center gap-1 mt-0.5">
                  <Lock className="w-2.5 h-2.5 text-primary/50" />
                  <span className="font-mono text-xs text-muted-foreground">Encrypted</span>
                  {room.ttlSeconds && <TTLLabel seconds={room.ttlSeconds} mode={room.ttlMode} />}
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
          />
        ) : (
          <div className="flex-1 flex flex-col items-center justify-center text-center px-6">
            <div className="w-16 h-16 bg-primary/10 border border-primary/20 flex items-center justify-center mb-6">
              <Shield className="w-8 h-8 text-primary" />
            </div>
            <h2 className="font-mono font-bold text-xl tracking-tight mb-3">QuantumShield</h2>
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
