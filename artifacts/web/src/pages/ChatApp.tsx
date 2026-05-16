import { useState, useEffect, useRef } from "react";
import { useLocation, Link } from "wouter";
import {
  Shield,
  Plus,
  LogOut,
  MessageSquare,
  Users,
  Clock,
  Lock,
  AlertTriangle,
  Send,
  X,
  Search,
  ChevronRight,
  ArrowLeft,
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
  useGetUsersSearch,
  getGetUsersSearchQueryKey,
  usePostRoomsRoomIdMembers,
  getGetRoomsRoomIdMembersQueryKey,
} from "@workspace/api-client-react";
import { useQueryClient } from "@tanstack/react-query";
import { clearAll } from "@/lib/auth";
import { encryptMessage, storeMessageKey, getMessageKey, decryptMessage, CIPHER_SUITE } from "@/lib/crypto";

type Room = {
  id: string;
  name?: string | null;
  type: "direct" | "group";
  memberCount: number;
  lastMessageAt?: string | null;
  ttlSeconds?: number | null;
  members?: Array<{ id: string; username: string; displayName?: string | null; avatarColor?: string | null }> | null;
};

type Message = {
  id: string;
  senderId: string;
  senderUsername?: string | null;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  expiresAt?: string | null;
  createdAt: string;
  _plaintext?: string;
};

function getRoomLabel(room: Room, currentUserId?: string): string {
  if (room.name) return room.name;
  if (room.type === "direct" && room.members) {
    const other = room.members.find((m) => m.id !== currentUserId);
    return other?.displayName ?? other?.username ?? "Direct Message";
  }
  return `Group (${room.memberCount})`;
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

function TTLLabel({ seconds }: { seconds?: number | null }) {
  if (!seconds) return null;
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const label = h > 0 ? `${h}h TTL` : `${m}m TTL`;
  return (
    <span className="font-mono text-xs text-primary/60 flex items-center gap-1">
      <Clock className="w-3 h-3" />
      {label}
    </span>
  );
}

function MessageExpiry({ expiresAt }: { expiresAt: string | null | undefined }) {
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
      {remaining}
    </span>
  );
}

function NewRoomDialog({ onClose, currentUserId }: { onClose: () => void; currentUserId: string }) {
  const qc = useQueryClient();
  const [name, setName] = useState("");
  const [type, setType] = useState<"direct" | "group">("direct");
  const [ttl, setTtl] = useState<number | null>(null);
  const [search, setSearch] = useState("");
  const [selectedIds, setSelectedIds] = useState<string[]>([]);

  const { data: searchResults } = useGetUsersSearch(
    { q: search },
    { query: { queryKey: getGetUsersSearchQueryKey({ q: search }), enabled: search.length > 0 } }
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
            <label className="font-mono text-xs text-muted-foreground block mb-2 tracking-widest">ADD MEMBERS</label>
            <div className="relative">
              <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-3.5 h-3.5 text-muted-foreground" />
              <input
                value={search}
                onChange={(e) => setSearch(e.target.value)}
                className="w-full bg-background border border-border pl-8 pr-3 py-2 font-mono text-sm focus:outline-none focus:border-primary/60"
                placeholder="Search username..."
                data-testid="input-search-users"
              />
            </div>

            {searchResults && searchResults.length > 0 && (
              <div className="border border-border mt-1 max-h-32 overflow-y-auto">
                {searchResults
                  .filter((u) => u.id !== currentUserId)
                  .map((u) => (
                    <button
                      key={u.id}
                      onClick={() => toggleUser(u.id)}
                      className={`w-full flex items-center gap-2 px-3 py-2 font-mono text-xs hover:bg-accent transition-colors text-left ${
                        selectedIds.includes(u.id) ? "bg-primary/10 text-primary" : ""
                      }`}
                      data-testid={`button-user-${u.id}`}
                    >
                      <div
                        className="w-5 h-5 rounded-full flex items-center justify-center text-white text-xs font-bold"
                        style={{ backgroundColor: u.avatarColor ?? "#06b6d4" }}
                      >
                        {u.username[0].toUpperCase()}
                      </div>
                      {u.displayName ?? u.username}
                      {selectedIds.includes(u.id) && <span className="ml-auto text-primary">SELECTED</span>}
                    </button>
                  ))}
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
    </div>
  );
}

function RoomView({ room, currentUserId, onBack }: { room: Room; currentUserId: string; onBack: () => void }) {
  const qc = useQueryClient();
  const [input, setInput] = useState("");
  const [decryptedMessages, setDecryptedMessages] = useState<Record<string, string>>({});
  const [cameraWarning, setCameraWarning] = useState(false);
  const messagesEndRef = useRef<HTMLDivElement>(null);
  const videoRef = useRef<HTMLVideoElement>(null);
  const detectionIntervalRef = useRef<ReturnType<typeof setInterval> | null>(null);

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

  const addMember = usePostRoomsRoomIdMembers({
    mutation: {
      onSuccess: () => {
        qc.invalidateQueries({ queryKey: getGetRoomsRoomIdMembersQueryKey(room.id) });
      },
    },
  });

  useEffect(() => {
    messagesEndRef.current?.scrollIntoView({ behavior: "smooth" });
  }, [messages]);

  useEffect(() => {
    let stream: MediaStream | null = null;

    const startCamera = async () => {
      try {
        stream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: "user" }, audio: false });
        if (videoRef.current) {
          videoRef.current.srcObject = stream;
          await videoRef.current.play();
        }

        const cocossd = await import("@tensorflow-models/coco-ssd" as any).catch(() => null);
        const tf = await import("@tensorflow/tfjs" as any).catch(() => null);
        if (!cocossd || !tf) return;

        const model = await cocossd.load();

        detectionIntervalRef.current = setInterval(async () => {
          if (!videoRef.current) return;
          try {
            const predictions = await model.detect(videoRef.current);
            const hasCamera = predictions.some((p: any) =>
              ["cell phone", "laptop", "tablet", "camera"].includes(p.class.toLowerCase())
            );
            setCameraWarning(hasCamera);
          } catch {}
        }, 1500);
      } catch {}
    };

    startCamera();

    return () => {
      if (detectionIntervalRef.current) clearInterval(detectionIntervalRef.current);
      if (stream) stream.getTracks().forEach((t) => t.stop());
    };
  }, []);

  const handleSend = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!input.trim()) return;
    const text = input;
    setInput("");

    const { ciphertext, nonce, key } = await encryptMessage(text);

    sendMessage.mutate(
      {
        roomId: room.id,
        data: {
          ciphertext,
          nonce,
          algorithm: CIPHER_SUITE,
          ttlSeconds: room.ttlSeconds,
        },
      },
      {
        onSuccess: (msg) => {
          storeMessageKey(msg.id, key);
          decryptMsg(msg as Message, key);
        },
      }
    );
  };

  const decryptMsg = async (msg: Message, key?: CryptoKey) => {
    const k = key ?? getMessageKey(msg.id);
    if (!k) return;
    try {
      const plaintext = await decryptMessage(msg.ciphertext, msg.nonce, k);
      setDecryptedMessages((prev) => ({ ...prev, [msg.id]: plaintext }));
    } catch {}
  };

  const isExpired = (expiresAt?: string | null) => {
    if (!expiresAt) return false;
    return new Date(expiresAt).getTime() < Date.now();
  };

  return (
    <div className="flex flex-col h-full relative">
      <video ref={videoRef} className="absolute w-0 h-0 opacity-0 pointer-events-none" playsInline muted />

      {cameraWarning && (
        <div className="bg-destructive/20 border-b border-destructive/50 px-4 py-2 flex items-center gap-2 z-10" data-testid="camera-warning">
          <AlertTriangle className="w-4 h-4 text-destructive animate-pulse flex-shrink-0" />
          <span className="font-mono text-xs text-destructive">
            RECORDING DEVICE DETECTED — SCREEN PROTECTION ACTIVE
          </span>
        </div>
      )}

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
              {getRoomLabel(room, currentUserId)}
            </h2>
            <TTLLabel seconds={room.ttlSeconds} />
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
        className="flex-1 overflow-y-auto p-4 space-y-3"
        style={{ filter: cameraWarning ? "blur(20px)" : "none" }}
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
          const plaintext = decryptedMessages[msg.id];

          return (
            <div
              key={msg.id}
              className={`flex ${isOwn ? "justify-end" : "justify-start"}`}
              data-testid={`message-${msg.id}`}
            >
              <div className={`max-w-[85%] md:max-w-[70%] ${isOwn ? "items-end" : "items-start"} flex flex-col gap-1`}>
                <div className="flex items-center gap-2">
                  {!isOwn && (
                    <span className="font-mono text-xs text-muted-foreground">
                      {msg.senderUsername}
                    </span>
                  )}
                  <MessageExpiry expiresAt={msg.expiresAt} />
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
                  ) : plaintext ? (
                    <p className="font-mono text-sm">{plaintext}</p>
                  ) : (
                    <div className="flex items-center gap-2 font-mono text-xs text-muted-foreground">
                      <Lock className="w-3 h-3" />
                      <button onClick={() => decryptMsg(msg as Message)} className="hover:text-primary">
                        Encrypted — tap to attempt decrypt
                      </button>
                    </div>
                  )}
                </div>
                <div className="flex items-center gap-2">
                  <span className="font-mono text-xs text-muted-foreground">
                    {formatTime(msg.createdAt)}
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
        style={{ filter: cameraWarning ? "blur(20px)" : "none", pointerEvents: cameraWarning ? "none" : "auto" }}
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
  const qc = useQueryClient();

  const { data: me } = useGetAuthMe();
  const { data: rooms = [] } = useGetRooms({ query: { queryKey: getGetRoomsQueryKey(), refetchInterval: 5000 } });

  const logout = usePostAuthLogout({
    mutation: {
      onSuccess: () => {
        clearAll();
        setLocation("/");
      },
    },
  });

  const activeRoom = rooms.find((r) => r.id === activeRoomId) as Room | undefined;

  return (
    <div className="h-screen bg-background flex overflow-hidden">
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
          <div className="flex items-center gap-2">
            <button
              onClick={() => logout.mutate()}
              className="text-muted-foreground hover:text-foreground transition-colors"
              title="Logout"
              data-testid="button-logout"
            >
              <LogOut className="w-4 h-4" />
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
                {me.username[0].toUpperCase()}
              </div>
              <div>
                <p className="font-mono text-xs font-semibold">{me.displayName ?? me.username}</p>
                <p className="font-mono text-xs text-muted-foreground">@{me.username}</p>
              </div>
            </div>
          </div>
        )}

        <div className="flex items-center justify-between px-4 py-2.5 border-b border-border/50">
          <span className="font-mono text-xs text-muted-foreground tracking-widest">CHANNELS</span>
          <button
            onClick={() => setShowNewRoom(true)}
            className="text-muted-foreground hover:text-primary transition-colors"
            data-testid="button-new-room"
          >
            <Plus className="w-4 h-4" />
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
                  : (room.members?.find((m) => m.id !== me?.id)?.username ?? "?")[0].toUpperCase()}
              </div>
              <div className="flex-1 min-w-0">
                <div className="flex items-center justify-between">
                  <p className="font-mono text-xs font-semibold truncate">
                    {getRoomLabel(room as Room, me?.id)}
                  </p>
                  {room.lastMessageAt && (
                    <span className="font-mono text-xs text-muted-foreground ml-2 flex-shrink-0">
                      {formatDate(room.lastMessageAt)}
                    </span>
                  )}
                </div>
                <div className="flex items-center gap-1 mt-0.5">
                  <Lock className="w-2.5 h-2.5 text-primary/50" />
                  <span className="font-mono text-xs text-muted-foreground">Encrypted</span>
                  {room.ttlSeconds && <TTLLabel seconds={room.ttlSeconds} />}
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

      {showNewRoom && me && (
        <NewRoomDialog
          onClose={() => setShowNewRoom(false)}
          currentUserId={me.id}
        />
      )}
    </div>
  );
}
