import { useState, useRef, useEffect, useCallback } from "react";
import {
  View,
  Text,
  StyleSheet,
  TouchableOpacity,
  TextInput,
  FlatList,
  ActivityIndicator,
  Modal,
  ScrollView,
  Platform,
  AppState,
  Linking,
} from "react-native";
import { useSafeAreaInsets } from "react-native-safe-area-context";
import { useRouter } from "expo-router";
import { Feather } from "@expo/vector-icons";
import { KeyboardAvoidingView } from "react-native-keyboard-controller";
import { CameraView, useCameraPermissions } from "expo-camera";
import { useQueryClient } from "@tanstack/react-query";
import { useColors } from "@/hooks/useColors";
import { useAuth } from "@/context/AuthContext";
import {
  useGetAuthMe,
  usePostAuthLogout,
  useGetRooms,
  getGetRoomsQueryKey,
  usePostRooms,
  useGetRoomsRoomIdMessages,
  getGetRoomsRoomIdMessagesQueryKey,
  usePostRoomsRoomIdMessages,
  useGetRoomsRoomIdMembers,
  getGetRoomsRoomIdMembersQueryKey,
  getRoomsRoomIdMembers,
  getKeysUserId,
  useGetUsersSearch,
  getGetUsersSearchQueryKey,
  getGetIdentityCodesQueryKey,
  useGetIdentityCodes,
  usePatchIdentityCodesCodeId,
  usePostIdentityCodes,
  type IdentityCode,
} from "@workspace/api-client-react";
import { gcm } from "@noble/ciphers/aes.js";
import { randomBytes } from "@noble/hashes/utils.js";
import { ml_kem1024 } from "@noble/post-quantum/ml-kem.js";
import * as ScreenCapture from "expo-screen-capture";
import * as LocalAuthentication from "expo-local-authentication";

const CIPHER_SUITE = "AES-256-GCM+ML-KEM-1024+ML-DSA-87";
const GITHUB_URL = "https://github.com/stevemoraco/qs";

function normalizeCodeInput(value: string): string {
  return value.trim().replace(/^[@#]+/, "").toLowerCase();
}

async function verifyDevice(promptMessage: string): Promise<void> {
  const hasHardware = await LocalAuthentication.hasHardwareAsync();
  const isEnrolled = await LocalAuthentication.isEnrolledAsync();
  if (!hasHardware || !isEnrolled) {
    throw new Error("Face ID or device biometrics are not set up.");
  }

  const result = await LocalAuthentication.authenticateAsync({
    promptMessage,
    fallbackLabel: "Use device passcode",
    disableDeviceFallback: false,
  });
  if (!result.success) throw new Error("Device verification was not completed.");
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
};

type WrappedMessageKey = {
  kemCiphertext: string;
  nonce: string;
  wrappedKey: string;
};

function getRoomLabel(room: Room, myId?: string): string {
  if (room.name) return room.name;
  if (room.type === "direct" && room.members) {
    const other = room.members.find((m) => m.id !== myId);
    return other?.displayName ?? other?.username ?? "Direct";
  }
  return `Group (${room.memberCount})`;
}

const CODE_NAMES = [
  "Axiom", "Beacon", "Cipher", "Delta", "Echo", "Flux", "Grid", "Halo",
  "Ion", "Junction", "Keystone", "Lumen", "Matrix", "Nova", "Obsidian", "Pulse",
  "Quartz", "Relay", "Signal", "Trace", "Unit", "Vector", "Ward", "Zenith",
];

type CodenameFor = (id: string) => string;

function createSessionCodenameFactory(): CodenameFor {
  const names = [...CODE_NAMES];
  const entropy = randomBytes(names.length);
  for (let i = names.length - 1; i > 0; i--) {
    const j = entropy[i] % (i + 1);
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

function FrontCameraSentinel({
  active,
  onStatus,
}: {
  active: boolean;
  onStatus: (status: "scanning" | "clear" | "unavailable", detail: string) => void;
}) {
  const [permission, requestPermission] = useCameraPermissions();

  useEffect(() => {
    let mounted = true;
    onStatus("scanning", "REQUESTING LOCAL SCAN");
    requestPermission()
      .then((result) => {
        if (!mounted) return;
        onStatus(result.granted ? "scanning" : "unavailable", result.granted ? "STARTING ON-DEVICE SCAN" : "CAMERA DENIED");
      })
      .catch(() => {
        if (mounted) onStatus("unavailable", "CAMERA PERMISSION ERROR");
      });
    return () => {
      mounted = false;
    };
  }, [onStatus, requestPermission]);

  useEffect(() => {
    if (!permission) return;
    if (!permission.granted) onStatus("unavailable", "CAMERA DENIED");
  }, [onStatus, permission]);

  if (!permission?.granted) return null;

  return (
    <CameraView
      style={styles.hiddenCamera}
      facing="front"
      active={active}
      mode="video"
      mute
      onCameraReady={() => onStatus("clear", "ON-DEVICE")}
      onMountError={() => onStatus("unavailable", "CAMERA MOUNT ERROR")}
    />
  );
}

function formatTime(iso: string): string {
  return new Date(iso).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
}

const messageKeyStore = new Map<string, Uint8Array>();

function bytesToB64(b: Uint8Array): string {
  let s = "";
  for (let i = 0; i < b.length; i++) s += String.fromCharCode(b[i]);
  return btoa(s);
}
function b64ToBytes(s: string): Uint8Array {
  const bin = atob(s);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}

async function encryptMsg(text: string): Promise<{ ciphertext: string; nonce: string; key: Uint8Array }> {
  const key = randomBytes(32);
  const nonce = randomBytes(12);
  const ct = gcm(key, nonce).encrypt(new TextEncoder().encode(text));
  return { ciphertext: bytesToB64(ct), nonce: bytesToB64(nonce), key };
}

async function decryptMsg(ciphertext: string, nonce: string, key: Uint8Array): Promise<string> {
  const pt = gcm(key, b64ToBytes(nonce)).decrypt(b64ToBytes(ciphertext));
  return new TextDecoder().decode(pt);
}

async function wrapMessageKeyForUser(userId: string, rawMessageKey: Uint8Array): Promise<string | null> {
  try {
    const bundle = await getKeysUserId(userId);
    const { cipherText, sharedSecret } = ml_kem1024.encapsulate(b64ToBytes(bundle.kemPublicKey));
    const nonce = randomBytes(12);
    const wrappedKey = gcm(sharedSecret, nonce).encrypt(rawMessageKey);
    return JSON.stringify({
      kemCiphertext: bytesToB64(cipherText),
      nonce: bytesToB64(nonce),
      wrappedKey: bytesToB64(wrappedKey),
    } satisfies WrappedMessageKey);
  } catch {
    return null;
  }
}

function unwrapMessageKey(wrappedValue: string, kemSecretKeyB64: string): Uint8Array | null {
  try {
    const wrapped = JSON.parse(wrappedValue) as WrappedMessageKey;
    const sharedSecret = ml_kem1024.decapsulate(b64ToBytes(wrapped.kemCiphertext), b64ToBytes(kemSecretKeyB64));
    return gcm(sharedSecret, b64ToBytes(wrapped.nonce)).decrypt(b64ToBytes(wrapped.wrappedKey));
  } catch {
    return null;
  }
}

function RoomListItem({ room, myId, active, onPress, colors, codenameForRoom }: {
  room: Room;
  myId?: string;
  active: boolean;
  onPress: () => void;
  colors: ReturnType<typeof useColors>;
  codenameForRoom: CodenameFor;
}) {
  const [revealName, setRevealName] = useState(false);
  const label = revealName ? getRoomLabel(room, myId) : codenameForRoom(room.id);
  const initial = label[0]?.toUpperCase() ?? "?";
  const avatarColor = room.members?.find((m) => m.id !== myId)?.avatarColor ?? colors.primary;

  return (
    <TouchableOpacity
      onPress={onPress}
      delayLongPress={180}
      onLongPress={() => setRevealName(true)}
      onPressOut={() => setRevealName(false)}
      style={[styles.roomItem, active && { backgroundColor: colors.card, borderLeftWidth: 2, borderLeftColor: colors.primary }]}
      testID={`button-room-${room.id}`}
    >
      <View style={[styles.avatar, { backgroundColor: avatarColor }]}> 
        <Text style={[styles.avatarText, { color: "#fff" }]}>{initial}</Text>
      </View>
      <View style={{ flex: 1 }}>
        <Text style={[styles.roomName, { color: colors.foreground }]} numberOfLines={1}>{label}</Text>
        <View style={styles.roomMeta}>
          <Feather name="lock" size={10} color={colors.primary} />
          <Text style={[styles.roomSub, { color: colors.mutedForeground }]}>E2E Encrypted</Text>
          {room.ttlSeconds && (
            <Text style={[styles.roomSub, { color: colors.primary }]}>· {room.ttlMode === "after_send" ? "TTL after send" : "TTL after view"}</Text>
          )}
        </View>
      </View>
      {room.lastMessageAt && (
        <Text style={[styles.roomTime, { color: colors.mutedForeground }]}>{formatTime(room.lastMessageAt)}</Text>
      )}
    </TouchableOpacity>
  );
}

function MessageBubble({ msg, isOwn, colors, plaintext, senderLabel, onRevealStart, onRevealEnd }: {
  msg: Message;
  isOwn: boolean;
  colors: ReturnType<typeof useColors>;
  plaintext?: string;
  senderLabel: string;
  onRevealStart: () => void;
  onRevealEnd: () => void;
}) {
  const expired = msg.expiresAt ? new Date(msg.expiresAt).getTime() < Date.now() : false;

  return (
    <View style={[styles.bubbleRow, isOwn && styles.bubbleRowOwn]}>
      <View style={[
        styles.bubble,
        { borderColor: colors.border },
        isOwn ? { backgroundColor: `${colors.primary}20`, borderColor: `${colors.primary}40` } : { backgroundColor: colors.card },
      ]}>
        {!isOwn && <Text style={[styles.senderName, { color: colors.primary }]}>{senderLabel}</Text>}
        {expired ? (
          <Text style={[styles.msgText, { color: colors.mutedForeground, fontStyle: "italic" }]}>Message expired — key destroyed</Text>
        ) : (
          <TouchableOpacity
            activeOpacity={0.85}
            delayLongPress={120}
            onPressIn={onRevealStart}
            onPressOut={onRevealEnd}
            onLongPress={onRevealStart}
            style={styles.encryptedRow}
            testID={`button-hold-reveal-${msg.id}`}
          >
            {plaintext ? (
              <Text style={[styles.msgText, { color: colors.foreground }]}>{plaintext}</Text>
            ) : (
              <>
                <Feather name="lock" size={12} color={colors.mutedForeground} />
                <Text style={[styles.msgText, { color: colors.mutedForeground }]}>Encrypted — hold to reveal</Text>
              </>
            )}
          </TouchableOpacity>
        )}
        <Text style={[styles.msgTime, { color: colors.mutedForeground }]}>{formatTime(msg.createdAt)}</Text>
      </View>
    </View>
  );
}

function ChatView({
  room,
  myId,
  colors,
  onBack,
  topPad,
  codenameForUser,
  roomCodename,
}: {
  room: Room;
  myId: string;
  colors: ReturnType<typeof useColors>;
  onBack: () => void;
  topPad: number;
  codenameForUser: CodenameFor;
  roomCodename: string;
}) {
  const qc = useQueryClient();
  const { getKemSecretKey } = useAuth();
  const [input, setInput] = useState("");
  const [heldPlaintext, setHeldPlaintext] = useState<{ id: string; text: string } | null>(null);
  const [screenshotAlert, setScreenshotAlert] = useState(false);
  const [revealRoomName, setRevealRoomName] = useState(false);
  const revealTokenRef = useRef(0);
  const insets = useSafeAreaInsets();

  useEffect(() => {
    let mounted = true;
    let sub: { remove: () => void } | undefined;
    let hideTimer: ReturnType<typeof setTimeout> | undefined;
    (async () => {
      try {
        await ScreenCapture.preventScreenCaptureAsync("quantumshield-chat");
      } catch {}
      if (!mounted) {
        ScreenCapture.allowScreenCaptureAsync("quantumshield-chat").catch(() => {});
        return;
      }
      try {
        sub = ScreenCapture.addScreenshotListener(() => {
          if (!mounted) return;
          setScreenshotAlert(true);
          if (hideTimer) clearTimeout(hideTimer);
          hideTimer = setTimeout(() => {
            if (mounted) setScreenshotAlert(false);
          }, 4000);
        });
      } catch {}
    })();
    return () => {
      mounted = false;
      if (hideTimer) clearTimeout(hideTimer);
      sub?.remove();
      ScreenCapture.allowScreenCaptureAsync("quantumshield-chat").catch(() => {});
    };
  }, []);

  useEffect(() => {
    const sub = AppState.addEventListener("change", (state) => {
      if (state !== "active") setHeldPlaintext(null);
    });
    return () => sub.remove();
  }, []);

  const { data: messages = [] } = useGetRoomsRoomIdMessages(
    room.id, {},
    { query: { queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id), refetchInterval: 3000 } }
  );

  useEffect(() => {
    const purgeExpiredKeys = () => {
      const now = Date.now();
      for (const msg of messages as Message[]) {
        if (msg.expiresAt && new Date(msg.expiresAt).getTime() <= now) {
          messageKeyStore.delete(msg.id);
          if (heldPlaintext?.id === msg.id) hideRevealedMessage();
        }
      }
    };
    purgeExpiredKeys();
    const interval = setInterval(purgeExpiredKeys, 1000);
    return () => clearInterval(interval);
  }, [heldPlaintext?.id, messages]);

  const { data: members = [] } = useGetRoomsRoomIdMembers(room.id, {
    query: { queryKey: getGetRoomsRoomIdMembersQueryKey(room.id) },
  });

  const sendMsg = usePostRoomsRoomIdMessages({
    mutation: { onSuccess: () => qc.invalidateQueries({ queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id) }) },
  });

  const handleSend = async () => {
    const text = input.trim();
    if (!text) return;
    setInput("");
    const { ciphertext, nonce, key } = await encryptMsg(text);
    const freshMembers = await getRoomsRoomIdMembers(room.id).catch(() => members);
    const recipientIds = Array.from(new Set([myId, ...freshMembers.map((member) => member.id)]));
    const recipientEncryptedKeys: Record<string, string> = {};
    await Promise.all(
      recipientIds.map(async (userId) => {
        const wrapped = await wrapMessageKeyForUser(userId, key);
        if (wrapped) recipientEncryptedKeys[userId] = wrapped;
      })
    );
    sendMsg.mutate(
      { roomId: room.id, data: { ciphertext, nonce, algorithm: CIPHER_SUITE, recipientEncryptedKeys, ttlSeconds: room.ttlSeconds } },
      { onSuccess: (msg) => { messageKeyStore.set(msg.id, key); } }
    );
  };

  const revealMessage = async (msg: Message) => {
    const revealToken = ++revealTokenRef.current;
    let key = messageKeyStore.get(msg.id);
    if (!key && msg.recipientEncryptedKeys?.[myId]) {
      const kemSecretKey = await getKemSecretKey();
      if (kemSecretKey) {
        key = unwrapMessageKey(msg.recipientEncryptedKeys[myId], kemSecretKey) ?? undefined;
        if (key) messageKeyStore.set(msg.id, key);
      }
    }
    if (!key) return;
    try {
      const plaintext = await decryptMsg(msg.ciphertext, msg.nonce, key);
      if (revealToken !== revealTokenRef.current) return;
      setHeldPlaintext({ id: msg.id, text: plaintext });
    } catch {}
  };

  const hideRevealedMessage = () => {
    revealTokenRef.current += 1;
    setHeldPlaintext(null);
  };
  const reversed = [...messages].reverse();

  return (
    <KeyboardAvoidingView style={{ flex: 1 }} behavior="padding" keyboardVerticalOffset={0}>
      <View style={[styles.chatHeader, { paddingTop: topPad + 10, borderBottomColor: colors.border }]}> 
        <TouchableOpacity onPress={onBack} style={styles.backBtn} testID="button-back-to-channels">
          <Feather name="chevron-left" size={24} color={colors.primary} />
        </TouchableOpacity>
        <View style={{ flex: 1, minWidth: 0 }}>
          <TouchableOpacity delayLongPress={120} onLongPress={() => setRevealRoomName(true)} onPressOut={() => setRevealRoomName(false)} activeOpacity={0.85} testID="button-hold-reveal-room-name">
            <Text style={[styles.chatTitle, { color: colors.foreground }]} numberOfLines={1}>{revealRoomName ? getRoomLabel(room, myId) : roomCodename}</Text>
          </TouchableOpacity>
          <View style={styles.cipherRow}>
            <Feather name="shield" size={10} color={colors.primary} />
            <Text style={[styles.cipherText, { color: colors.primary }]} numberOfLines={1}>{CIPHER_SUITE}</Text>
          </View>
        </View>
        <View style={styles.memberBadge}>
          <Feather name="users" size={12} color={colors.mutedForeground} />
          <Text style={[styles.memberCount, { color: colors.mutedForeground }]}>{members.length}</Text>
        </View>
      </View>
      {screenshotAlert && (
        <View style={[styles.screenshotAlert, { backgroundColor: "#ef4444" }]} testID="screenshot-alert">
          <Feather name="alert-triangle" size={12} color="#fff" />
          <Text style={styles.screenshotAlertText}>SCREENSHOT DETECTED — ROOM PRIVACY MAY BE COMPROMISED</Text>
        </View>
      )}

      <FlatList
        data={reversed}
        keyExtractor={(m) => m.id}
        inverted
        contentContainerStyle={{ padding: 16 }}
        renderItem={({ item }) => {
          const plaintext = heldPlaintext?.id === item.id ? heldPlaintext.text : undefined;
          return (
            <MessageBubble
              msg={item as Message}
              isOwn={item.senderId === myId}
              colors={colors}
              plaintext={plaintext}
              senderLabel={plaintext ? (item.senderUsername ?? codenameForUser(item.senderId)) : codenameForUser(item.senderId)}
              onRevealStart={() => revealMessage(item as Message)}
              onRevealEnd={hideRevealedMessage}
            />
          );
        }}
        ListEmptyComponent={
          <View style={styles.emptyChat}>
            <Feather name="lock" size={40} color={colors.border} />
            <Text style={[styles.emptyChatText, { color: colors.mutedForeground }]}>No messages yet</Text>
            <Text style={[styles.emptyChatSub, { color: colors.mutedForeground }]}>All messages are end-to-end encrypted</Text>
          </View>
        }
        keyboardShouldPersistTaps="handled"
        keyboardDismissMode="interactive"
        onScrollBeginDrag={hideRevealedMessage}
        showsVerticalScrollIndicator={false}
        scrollEnabled={!!messages.length}
      />

      <View style={[styles.inputBar, { borderTopColor: colors.border, paddingBottom: insets.bottom + 8 }]}> 
        <TextInput
          style={[styles.msgInput, { backgroundColor: colors.card, borderColor: colors.border, color: colors.foreground }]}
          value={input}
          onChangeText={setInput}
          placeholder="Message — encrypted client-side..."
          placeholderTextColor={colors.mutedForeground}
          multiline
          testID="input-message"
        />
        <TouchableOpacity onPress={handleSend} disabled={!input.trim() || sendMsg.isPending} style={[styles.sendBtn, { backgroundColor: colors.primary }, (!input.trim() || sendMsg.isPending) && { opacity: 0.4 }]} testID="button-send">
          <Feather name="send" size={16} color={colors.background} />
        </TouchableOpacity>
      </View>
    </KeyboardAvoidingView>
  );
}

function NewRoomModal({ visible, onClose, myId, colors, codenameForUser }: {
  visible: boolean;
  onClose: () => void;
  myId: string;
  colors: ReturnType<typeof useColors>;
  codenameForUser: CodenameFor;
}) {
  const qc = useQueryClient();
  const [name, setName] = useState("");
  const [type, setType] = useState<"direct" | "group">("direct");
  const [ttl, setTtl] = useState<number | null>(300);
  const [ttlMode, setTtlMode] = useState<"after_view" | "after_send">("after_view");
  const [pendingTtlMode, setPendingTtlMode] = useState<"after_view" | "after_send" | null>(null);
  const [search, setSearch] = useState("");
  const [selected, setSelected] = useState<string[]>([]);

  const normalizedSearch = normalizeCodeInput(search);
  const { data: results = [] } = useGetUsersSearch(
    { q: normalizedSearch },
    { query: { queryKey: getGetUsersSearchQueryKey({ q: normalizedSearch }), enabled: normalizedSearch.length > 0 } }
  );

  const createRoom = usePostRooms({
    mutation: {
      onSuccess: () => {
        qc.invalidateQueries({ queryKey: getGetRoomsQueryKey() });
        onClose();
        setName(""); setSearch(""); setSelected([]); setTtl(300); setTtlMode("after_view");
      },
    },
  });

  const TTL_OPTIONS = [
    { label: "No expiry", v: null },
    { label: "5 min", v: 300 },
    { label: "1 hour", v: 3600 },
    { label: "24 hours", v: 86400 },
    { label: "7 days", v: 604800 },
  ];

  return (
    <Modal visible={visible} animationType="slide" presentationStyle="pageSheet" onRequestClose={onClose}>
      <View style={[styles.modal, { backgroundColor: colors.background }]}> 
        <View style={[styles.modalHeader, { borderBottomColor: colors.border }]}> 
          <Text style={[styles.modalTitle, { color: colors.foreground }]}>NEW CHANNEL</Text>
          <TouchableOpacity onPress={onClose} testID="button-close-dialog"><Feather name="x" size={20} color={colors.mutedForeground} /></TouchableOpacity>
        </View>

        <ScrollView contentContainerStyle={styles.modalBody} keyboardShouldPersistTaps="handled">
          <Text style={[styles.label, { color: colors.mutedForeground }]}>CHANNEL NAME</Text>
          <TextInput style={[styles.input, { backgroundColor: colors.card, borderColor: colors.border, color: colors.foreground }]} value={name} onChangeText={setName} placeholder="Optional name..." placeholderTextColor={colors.mutedForeground} testID="input-room-name" />

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>TYPE</Text>
          <View style={styles.typeRow}>
            {(["direct", "group"] as const).map((t) => (
              <TouchableOpacity key={t} onPress={() => setType(t)} style={[styles.typeBtn, { borderColor: type === t ? colors.primary : colors.border }, type === t && { backgroundColor: `${colors.primary}20` }]} testID={`button-type-${t}`}>
                <Text style={[styles.typeBtnText, { color: type === t ? colors.primary : colors.mutedForeground }]}>{t.toUpperCase()}</Text>
              </TouchableOpacity>
            ))}
          </View>

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>MESSAGE EXPIRY (TTL)</Text>
          <ScrollView horizontal showsHorizontalScrollIndicator={false} style={styles.ttlScroll}>
            {TTL_OPTIONS.map((o) => (
              <TouchableOpacity key={String(o.v)} onPress={() => setTtl(o.v)} style={[styles.ttlBtn, { borderColor: ttl === o.v ? colors.primary : colors.border }, ttl === o.v && { backgroundColor: `${colors.primary}20` }]}>
                <Text style={[styles.ttlBtnText, { color: ttl === o.v ? colors.primary : colors.mutedForeground }]}>{o.label}</Text>
              </TouchableOpacity>
            ))}
          </ScrollView>

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>TTL STARTS</Text>
          <View style={styles.typeRow}>
            {[
              { label: "AFTER VIEW", v: "after_view" as const },
              { label: "AFTER SEND", v: "after_send" as const },
            ].map((o) => (
              <TouchableOpacity key={o.v} onPress={() => o.v !== ttlMode && setPendingTtlMode(o.v)} style={[styles.typeBtn, { borderColor: ttlMode === o.v ? colors.primary : colors.border }, ttlMode === o.v && { backgroundColor: `${colors.primary}20` }]}>
                <Text style={[styles.typeBtnText, { color: ttlMode === o.v ? colors.primary : colors.mutedForeground }]}>{o.label}</Text>
              </TouchableOpacity>
            ))}
          </View>

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>ADD MEMBERS</Text>
          <View style={[styles.searchRow, { backgroundColor: colors.card, borderColor: colors.border }]}> 
            <Feather name="search" size={14} color={colors.mutedForeground} />
            <TextInput style={[styles.searchInput, { color: colors.foreground }]} value={search} onChangeText={setSearch} placeholder="Search code..." placeholderTextColor={colors.mutedForeground} autoCapitalize="none" testID="input-search-users" />
          </View>

          {results.filter((u) => u.id !== myId).map((u) => {
            const label = codenameForUser(u.id);
            return (
              <TouchableOpacity key={u.id} onPress={() => setSelected((s) => s.includes(u.id) ? s.filter((x) => x !== u.id) : [...s, u.id])} style={[styles.userRow, selected.includes(u.id) && { backgroundColor: `${colors.primary}15` }]} testID={`button-user-${u.id}`}>
                <View style={[styles.avatarSm, { backgroundColor: u.avatarColor ?? colors.primary }]}> 
                  <Text style={styles.avatarText}>{label[0]}</Text>
                </View>
                <Text style={[styles.userName, { color: colors.foreground }]}>{label}</Text>
                {selected.includes(u.id) && <Feather name="check-circle" size={16} color={colors.primary} />}
              </TouchableOpacity>
            );
          })}

          <TouchableOpacity style={[styles.createBtn, { backgroundColor: colors.primary }, createRoom.isPending && { opacity: 0.5 }]} onPress={() => createRoom.mutate({ data: { name: name || null, type, memberIds: selected, ttlSeconds: ttl, ttlMode } })} disabled={createRoom.isPending} testID="button-create-room">
            {createRoom.isPending ? <ActivityIndicator color={colors.background} size="small" /> : <Text style={[styles.createBtnText, { color: colors.background }]}>CREATE ENCRYPTED CHANNEL</Text>}
          </TouchableOpacity>
        </ScrollView>
        {pendingTtlMode && (
          <Modal transparent animationType="fade" visible onRequestClose={() => setPendingTtlMode(null)}>
            <View style={styles.confirmOverlay}>
              <View style={[styles.confirmBox, { backgroundColor: colors.card, borderColor: colors.border }]}>
                <Text style={[styles.confirmKicker, { color: colors.primary }]}>EXPIRY MODE</Text>
                <Text style={[styles.confirmTitle, { color: colors.foreground }]}>
                  {pendingTtlMode === "after_view" ? "Start TTL after first view?" : "Start TTL after send?"}
                </Text>
                <Text style={[styles.confirmText, { color: colors.mutedForeground }]}>
                  {pendingTtlMode === "after_view"
                    ? "Messages stay available until the room is opened and fetched, then the countdown starts. This is the default for ephemeral conversations."
                    : "Messages begin expiring immediately when sent, even if nobody has viewed them yet."}
                </Text>
                <View style={styles.confirmActions}>
                  <TouchableOpacity onPress={() => setPendingTtlMode(null)} style={[styles.confirmBtn, { borderColor: colors.border }]}>
                    <Text style={[styles.confirmBtnText, { color: colors.mutedForeground }]}>CANCEL</Text>
                  </TouchableOpacity>
                  <TouchableOpacity onPress={() => { setTtlMode(pendingTtlMode); setPendingTtlMode(null); }} style={[styles.confirmBtn, { borderColor: colors.primary, backgroundColor: `${colors.primary}20` }]}>
                    <Text style={[styles.confirmBtnText, { color: colors.primary }]}>USE MODE</Text>
                  </TouchableOpacity>
                </View>
              </View>
            </View>
          </Modal>
        )}
      </View>
    </Modal>
  );
}

const CODE_TTL_OPTIONS = [
  { label: "5 min", value: 300 },
  { label: "1 hour", value: 3600 },
  { label: "1 day", value: 86400 },
  { label: "1 month", value: 2592000 },
  { label: "1 year", value: 31536000 },
  { label: "10 years", value: 315360000 },
];

const CODE_SCOPE_OPTIONS = [
  { label: "Public", value: "public" },
  { label: "Invited by you", value: "invited_by_you" },
  { label: "Invited you", value: "invited_you" },
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
  const abs = expiry.toLocaleString();
  if (diff <= 0) return `${abs} / expired`;
  const minutes = Math.floor(diff / 60000);
  const days = Math.floor(minutes / 1440);
  const hours = Math.floor((minutes % 1440) / 60);
  const mins = minutes % 60;
  return `${abs} / ${days > 0 ? `${days}d ${hours}h` : hours > 0 ? `${hours}h ${mins}m` : `${mins}m`} remaining`;
}

function ProfileModal({ visible, onClose, me, colors, codename, token }: {
  visible: boolean;
  onClose: () => void;
  me: { id: string; username: string; displayName?: string | null; avatarColor?: string | null };
  colors: ReturnType<typeof useColors>;
  codename: string;
  token: string | null;
}) {
  const qc = useQueryClient();
  const { getDevicePasscode, setAuthHandle, setToken } = useAuth();
  const [revealed, setRevealed] = useState(false);
  const [deviceCount, setDeviceCount] = useState<number | null>(null);
  const [newCode, setNewCode] = useState("");
  const [newKind, setNewKind] = useState<"alias" | "invite">("alias");
  const [newTtl, setNewTtl] = useState(315360000);
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
  const { data: codes = [] } = useGetIdentityCodes({ query: { queryKey: getGetIdentityCodesQueryKey(), enabled: visible } });
  const sortedCodes = [...codes].sort((a, b) => `${a.kind}:${a.active ? "0" : "1"}:${a.code}:${a.createdAt}`.localeCompare(`${b.kind}:${b.active ? "0" : "1"}:${b.code}:${b.createdAt}`));
  const activeHandleCount = codes.filter((code) => code.kind === "alias" && code.active).length;

  useEffect(() => {
    if (!visible || !revealed || !token) return;
    let mounted = true;
    const url = Platform.OS === "web" ? "/api/auth/devices" : `https://${process.env.EXPO_PUBLIC_DOMAIN}/api/auth/devices`;
    fetch(url, { headers: { Authorization: `Bearer ${token}` } })
      .then((res) => (res.ok ? res.json() : null))
      .then((data) => {
        if (mounted && data && typeof data.activeDeviceCount === "number") setDeviceCount(data.activeDeviceCount);
      })
      .catch(() => {
        if (mounted) setDeviceCount(null);
      });
    return () => {
      mounted = false;
    };
  }, [revealed, token, visible]);

  const createCode = usePostIdentityCodes({
    mutation: {
      onSuccess: () => {
        setNewCode("");
        setError("");
        qc.invalidateQueries({ queryKey: getGetIdentityCodesQueryKey() });
      },
      onError: () => setError("Could not create code"),
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

  const submitCode = () => {
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
        await verifyDevice("Confirm last handle disable");
        const passcode = await getDevicePasscode();
        if (!passcode) throw new Error("No local device access key found.");
        const url = Platform.OS === "web" ? "/api/auth/login" : `https://${process.env.EXPO_PUBLIC_DOMAIN}/api/auth/login`;
        const res = await fetch(url, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ handle: pendingUpdate.code.code, passcode }),
        });
        const auth = await res.json();
        if (!res.ok) throw new Error(auth?.error ?? "Fresh device verification failed.");
        await setToken(auth.token);
        await setAuthHandle(auth.authHandle);
        data = { ...data, confirmLastHandleDisable: true };
      } catch (err: unknown) {
        setError(err instanceof Error ? err.message : "Fresh device verification failed.");
        return;
      }
    }
    updateCode.mutate({ codeId: pendingUpdate.code.id, data });
  };

  return (
    <Modal visible={visible} animationType="slide" presentationStyle="pageSheet" onRequestClose={onClose}>
      <View style={[styles.modal, { backgroundColor: colors.background }]}> 
        <View style={[styles.modalHeader, { borderBottomColor: colors.border }]}> 
          <Text style={[styles.modalTitle, { color: colors.foreground }]}>PROFILE / IDS</Text>
          <TouchableOpacity onPress={onClose} testID="button-close-profile"><Feather name="x" size={20} color={colors.mutedForeground} /></TouchableOpacity>
        </View>

        <ScrollView contentContainerStyle={styles.modalBody} keyboardShouldPersistTaps="handled">
          <View style={[styles.profileBlock, { borderColor: colors.border, backgroundColor: colors.card }]}> 
            <View style={[styles.avatarSm, { backgroundColor: me.avatarColor ?? colors.primary }]}> 
              <Text style={styles.avatarText}>{codename[0]}</Text>
            </View>
            <View style={{ flex: 1 }}>
              <TouchableOpacity delayLongPress={120} onLongPress={() => setRevealed(true)} onPressOut={() => setRevealed(false)} activeOpacity={0.85} testID="button-hold-reveal-profile">
                <Text style={[styles.meUsername, { color: colors.foreground }]}>{revealed ? (me.displayName ?? me.username) : codename}</Text>
              </TouchableOpacity>
              <Text style={[styles.meHandle, { color: colors.mutedForeground }]}>
                {revealed ? `${deviceCount ?? "..."} active linked device session${deviceCount === 1 ? "" : "s"}` : "Hold to reveal device links"}
              </Text>
            </View>
          </View>

          <Text style={[styles.label, { color: colors.mutedForeground }]}>CREATE HANDLE / INVITE</Text>
          <TextInput
            style={[styles.input, { backgroundColor: colors.card, borderColor: colors.border, color: colors.foreground }]}
            value={newCode}
            onChangeText={setNewCode}
            placeholder="@marlin or blank for random"
            placeholderTextColor={colors.mutedForeground}
            autoCapitalize="none"
            testID="input-new-identity-code"
          />
          <View style={[styles.typeRow, { marginTop: 10 }]}>
            {(["alias", "invite"] as const).map((kind) => (
              <TouchableOpacity key={kind} onPress={() => setNewKind(kind)} style={[styles.typeBtn, { borderColor: newKind === kind ? colors.primary : colors.border }, newKind === kind && { backgroundColor: `${colors.primary}20` }]}>
                <Text style={[styles.typeBtnText, { color: newKind === kind ? colors.primary : colors.mutedForeground }]}>{kind === "alias" ? "HANDLE" : "INVITE"}</Text>
              </TouchableOpacity>
            ))}
          </View>
          <Text style={[styles.codeMeta, { color: colors.mutedForeground, marginTop: 8 }]}>{describeCodeKind(newKind)}</Text>
          <Text style={[styles.codeMeta, { color: colors.primary, marginTop: 8 }]}>New handles and invites are public when created. You can restrict or disable them after creation.</Text>
          <ScrollView horizontal showsHorizontalScrollIndicator={false} style={styles.ttlScroll}>
            {CODE_TTL_OPTIONS.map((ttl) => (
              <TouchableOpacity key={ttl.value} onPress={() => setNewTtl(ttl.value)} style={[styles.ttlBtn, { borderColor: newTtl === ttl.value ? colors.primary : colors.border }, newTtl === ttl.value && { backgroundColor: `${colors.primary}20` }]}>
                <Text style={[styles.ttlBtnText, { color: newTtl === ttl.value ? colors.primary : colors.mutedForeground }]}>{ttl.label}</Text>
              </TouchableOpacity>
            ))}
          </ScrollView>
          {!!error && <Text style={[styles.errorText, { color: colors.destructive }]}>{error}</Text>}
          <TouchableOpacity style={[styles.createBtn, { backgroundColor: colors.primary }, createCode.isPending && { opacity: 0.5 }]} onPress={submitCode} disabled={createCode.isPending} testID="button-create-identity-code">
            {createCode.isPending ? <ActivityIndicator color={colors.background} size="small" /> : <Text style={[styles.createBtnText, { color: colors.background }]}>CREATE CODE</Text>}
          </TouchableOpacity>

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 24 }]}>YOUR HANDLES / INVITES</Text>
          {codes.length === 0 && <Text style={[styles.emptyText, { color: colors.mutedForeground }]}>No handles or invite codes yet.</Text>}
          {sortedCodes.map((code) => (
            <View key={code.id} style={[styles.codeCard, { borderColor: colors.border, backgroundColor: colors.card }]} testID={`identity-code-${code.id}`}>
              <View style={styles.codeHeader}>
                <View style={{ flex: 1 }}>
                  <Text style={[styles.codeTitle, { color: colors.foreground }]}>{code.kind === "alias" ? "@" : "#"}{code.code}</Text>
                  <Text style={[styles.codeMeta, { color: colors.mutedForeground }]}>{code.active ? "ACTIVE" : "DISABLED"} / {code.visibilityScope.replaceAll("_", " ")} / {code.useCount}{code.maxUses ? ` of ${code.maxUses}` : ""} uses</Text>
                  <Text style={[styles.codeMeta, { color: colors.mutedForeground }]}>{formatExpiry(code.expiresAt)}</Text>
                </View>
                <TouchableOpacity disabled={updateCode.isPending} onPress={() => requestUpdate(`${code.active ? "Disable" : "Enable"} ${code.code}? This changes whether people can discover or link with it.`, code, { active: !code.active })} style={[styles.smallBtn, { borderColor: colors.border }, updateCode.isPending && { opacity: 0.5 }]}>
                  <Text style={[styles.smallBtnText, { color: colors.primary }]}>{code.active ? "DISABLE" : "ENABLE"}</Text>
                </TouchableOpacity>
              </View>
              <ScrollView horizontal showsHorizontalScrollIndicator={false} style={styles.ttlScroll}>
                {CODE_SCOPE_OPTIONS.map((scope) => (
                  <TouchableOpacity key={scope.value} disabled={updateCode.isPending} onPress={() => requestUpdate(`Change visibility for ${code.code} to ${scope.label}?`, code, { visibilityScope: scope.value })} style={[styles.ttlBtn, { borderColor: code.visibilityScope === scope.value ? colors.primary : colors.border }, updateCode.isPending && { opacity: 0.5 }]}>
                    <Text style={[styles.ttlBtnText, { color: code.visibilityScope === scope.value ? colors.primary : colors.mutedForeground }]}>{scope.label}</Text>
                  </TouchableOpacity>
                ))}
              </ScrollView>
              <ScrollView horizontal showsHorizontalScrollIndicator={false} style={styles.ttlScroll}>
                {CODE_TTL_OPTIONS.map((ttl) => (
                  <TouchableOpacity key={ttl.value} disabled={updateCode.isPending} onPress={() => requestUpdate(`Change duration for ${code.code} to ${ttl.label}?`, code, { ttlSeconds: ttl.value })} style={[styles.ttlBtn, { borderColor: colors.border }, updateCode.isPending && { opacity: 0.5 }]}>
                    <Text style={[styles.ttlBtnText, { color: colors.mutedForeground }]}>{ttl.label}</Text>
                  </TouchableOpacity>
                ))}
                <TouchableOpacity disabled={updateCode.isPending} onPress={() => requestUpdate(`Roll/expire ${code.code}? This disables it immediately.`, code, { active: false, visibilityScope: "disabled" })} style={[styles.ttlBtn, { borderColor: colors.destructive }, updateCode.isPending && { opacity: 0.5 }]}>
                  <Text style={[styles.ttlBtnText, { color: colors.destructive }]}>Roll / expire</Text>
                </TouchableOpacity>
              </ScrollView>
            </View>
          ))}
        </ScrollView>
        {pendingUpdate && (
          <ConfirmCodeUpdateModal
            pendingUpdate={pendingUpdate}
            updatePending={updateCode.isPending}
            colors={colors}
            onCancel={() => setPendingUpdate(null)}
            onConfirm={() => void confirmPendingUpdate()}
          />
        )}
      </View>
    </Modal>
  );
}

function ConfirmCodeUpdateModal({
  pendingUpdate,
  updatePending,
  colors,
  onCancel,
  onConfirm,
}: {
  pendingUpdate: { code: IdentityCode; message: string; isLastActiveHandle: boolean; stage: number };
  updatePending: boolean;
  colors: ReturnType<typeof useColors>;
  onCancel: () => void;
  onConfirm: () => void;
}) {
  return (
    <Modal transparent animationType="fade" visible onRequestClose={onCancel}>
      <View style={styles.confirmOverlay}>
        <View style={[styles.confirmBox, { backgroundColor: colors.card, borderColor: colors.border }]}>
          <View style={styles.confirmTitleRow}>
            <Feather name="shield" size={16} color={pendingUpdate.isLastActiveHandle ? colors.destructive : colors.primary} />
            <Text style={[styles.confirmKicker, { color: colors.mutedForeground }]}>
              {pendingUpdate.isLastActiveHandle ? `LAST HANDLE CONFIRM ${pendingUpdate.stage}/3` : "CONFIRM CHANGE"}
            </Text>
          </View>
          <Text style={[styles.confirmTitle, { color: colors.foreground }]}>
            {pendingUpdate.isLastActiveHandle ? `Disable @${pendingUpdate.code.code}?` : "Apply this change?"}
          </Text>
          <Text style={[styles.confirmText, { color: colors.mutedForeground }]}>
            {pendingUpdate.isLastActiveHandle
              ? "This is your last active handle. If you disable it and then log out, you may not be able to recover this account. The final confirmation requires Face ID or device verification."
              : pendingUpdate.message}
          </Text>
          {pendingUpdate.isLastActiveHandle && (
            <Text style={[styles.confirmDanger, { color: colors.destructive }]}>Step {pendingUpdate.stage} of 3: confirm you understand this can lock you out.</Text>
          )}
          <View style={styles.confirmActions}>
            <TouchableOpacity onPress={onCancel} style={[styles.confirmBtn, { borderColor: colors.border }]}>
              <Text style={[styles.confirmBtnText, { color: colors.mutedForeground }]}>CANCEL</Text>
            </TouchableOpacity>
            <TouchableOpacity disabled={updatePending} onPress={onConfirm} style={[styles.confirmBtn, { borderColor: colors.destructive, backgroundColor: `${colors.destructive}20` }, updatePending && { opacity: 0.5 }]}>
              <Text style={[styles.confirmBtnText, { color: colors.destructive }]}>{pendingUpdate.isLastActiveHandle && pendingUpdate.stage === 3 ? "VERIFY DEVICE" : "CONFIRM"}</Text>
            </TouchableOpacity>
          </View>
        </View>
      </View>
    </Modal>
  );
}

export default function AppScreen() {
  const colors = useColors();
  const insets = useSafeAreaInsets();
  const router = useRouter();
  const qc = useQueryClient();
  const { clearAuth, token } = useAuth();
  const codenameForRef = useRef<CodenameFor | null>(null);
  if (!codenameForRef.current) codenameForRef.current = createSessionCodenameFactory();
  const codenameFor = codenameForRef.current;

  const [activeRoomId, setActiveRoomId] = useState<string | null>(null);
  const [showNewRoom, setShowNewRoom] = useState(false);
  const [showProfile, setShowProfile] = useState(false);
  const [showRooms, setShowRooms] = useState(true);
  const [revealedNameId, setRevealedNameId] = useState<string | null>(null);
  const [appActive, setAppActive] = useState(true);
  const [privacyLock, setPrivacyLock] = useState<{ active: boolean; reason: string; error?: string }>({ active: false, reason: "" });
  const [isUnlockingPrivacy, setIsUnlockingPrivacy] = useState(false);
  const privacyAutoUnlockAttemptedRef = useRef(false);
  const [cameraStatus, setCameraStatus] = useState<"scanning" | "clear" | "unavailable">("scanning");
  const [cameraDetail, setCameraDetail] = useState("REQUESTING LOCAL SCAN");
  const [cameraInfoOpen, setCameraInfoOpen] = useState(false);

  const { data: me } = useGetAuthMe();
  const { data: rooms = [] } = useGetRooms({ query: { queryKey: getGetRoomsQueryKey(), refetchInterval: 5000 } });

  const logout = usePostAuthLogout({
    mutation: { onSuccess: async () => { await clearAuth(); router.replace("/login"); } },
  });

  const activeRoom = rooms.find((r) => r.id === activeRoomId) as Room | undefined;
  const codenameForUser = useCallback((id: string) => codenameFor(`user:${id}`), [codenameFor]);
  const codenameForRoom = useCallback((id: string) => codenameFor(`room:${id}`), [codenameFor]);
  const updateCameraStatus = useCallback((status: "scanning" | "clear" | "unavailable", detail: string) => { setCameraStatus(status); setCameraDetail(detail); }, []);
  const lockPrivacy = useCallback((reason: string) => {
    setPrivacyLock((current) => {
      if (!current.active) privacyAutoUnlockAttemptedRef.current = false;
      return { active: true, reason: current.active ? current.reason : reason };
    });
  }, []);

  useEffect(() => {
    const sub = AppState.addEventListener("change", (state) => {
      const active = state === "active";
      setAppActive(active);
      if (!active) lockPrivacy("App left the foreground.");
    });
    return () => sub.remove();
  }, [lockPrivacy]);

  useEffect(() => {
    let mounted = true;
    let sub: { remove: () => void } | undefined;
    (async () => {
      try {
        await ScreenCapture.preventScreenCaptureAsync("quantumshield-app");
        if (!mounted) return;
        sub = ScreenCapture.addScreenshotListener(() => {
          if (mounted) lockPrivacy("Screenshot was detected.");
        });
      } catch {}
    })();
    return () => {
      mounted = false;
      sub?.remove();
      ScreenCapture.allowScreenCaptureAsync("quantumshield-app").catch(() => {});
    };
  }, [lockPrivacy]);

  const unlockPrivacy = async () => {
    setPrivacyLock((current) => ({ ...current, error: undefined }));
    setIsUnlockingPrivacy(true);
    try {
      await verifyDevice("Unlock QuantumShield");
      setPrivacyLock({ active: false, reason: "" });
    } catch (err: unknown) {
      setPrivacyLock((current) => ({
        ...current,
        active: true,
        error: err instanceof Error ? err.message : "Device verification failed.",
      }));
    } finally {
      setIsUnlockingPrivacy(false);
    }
  };

  useEffect(() => {
    if (!privacyLock.active || !appActive || isUnlockingPrivacy || privacyAutoUnlockAttemptedRef.current) return;
    privacyAutoUnlockAttemptedRef.current = true;
    const id = setTimeout(() => {
      void unlockPrivacy();
    }, 250);
    return () => clearTimeout(id);
  }, [privacyLock.active, privacyLock.reason, appActive, isUnlockingPrivacy]);

  const topPad = Platform.OS === "web" ? 67 : 0;
  const cameraColor = cameraStatus === "clear" ? colors.primary : colors.mutedForeground;

  return (
    <View style={[styles.root, { backgroundColor: colors.background }]}> 
      <FrontCameraSentinel active={appActive} onStatus={updateCameraStatus} />
      <TouchableOpacity
        activeOpacity={0.85}
        onPress={() => setCameraInfoOpen(true)}
        style={[styles.cameraStatus, { borderBottomColor: colors.border, paddingTop: (Platform.OS === "web" ? 6 : insets.top + 6) }]}
        testID="camera-status"
      >
        <View style={[styles.cameraDot, { backgroundColor: cameraColor }]} />
        <Text style={[styles.cameraStatusText, { color: cameraColor }]}>{cameraStatus === "clear" ? "PRIVACY ENSURED" : cameraStatus === "scanning" ? "STARTING PRIVACY SCAN" : "PRIVACY SCAN OFFLINE"} / {cameraDetail}</Text>
      </TouchableOpacity>
      <Modal visible={cameraInfoOpen} transparent animationType="fade" onRequestClose={() => setCameraInfoOpen(false)}>
        <View style={styles.confirmOverlay}>
          <View style={[styles.confirmBox, { backgroundColor: colors.card, borderColor: colors.primary }]}>
            <Text style={[styles.confirmTitle, { color: colors.primary }]}>WHY THE CAMERA IS ON</Text>
            <Text style={[styles.confirmText, { color: colors.mutedForeground }]}>
              QuantumShield uses your front camera locally to help detect nearby recording devices pointed at the screen. Frames stay on this device for privacy-shield decisions and are not uploaded or attached to messages.
            </Text>
            <View style={styles.confirmActions}>
              <TouchableOpacity onPress={() => setCameraInfoOpen(false)} style={[styles.confirmBtn, { backgroundColor: colors.primary, borderColor: colors.primary }]}>
                <Text style={[styles.confirmBtnText, { color: colors.background }]}>OK</Text>
              </TouchableOpacity>
            </View>
          </View>
        </View>
      </Modal>
      {privacyLock.active && (
        <View style={[styles.privacyLock, { backgroundColor: colors.background }]} testID="privacy-lock">
          <Feather name="shield" size={44} color={colors.primary} />
          <Text style={[styles.privacyLockTitle, { color: colors.primary }]}>PRIVACY SHIELD ACTIVE</Text>
          <Text style={[styles.privacyLockText, { color: colors.mutedForeground }]}>{privacyLock.reason || "Secure content is locked until device verification succeeds."}</Text>
          {!!privacyLock.error && <Text style={[styles.privacyLockText, { color: colors.destructive }]}>{privacyLock.error}</Text>}
          <TouchableOpacity
            onPress={unlockPrivacy}
            disabled={isUnlockingPrivacy}
            style={[styles.privacyUnlockButton, { backgroundColor: colors.primary }, isUnlockingPrivacy && { opacity: 0.5 }]}
            testID="button-unlock-privacy-shield"
          >
            {isUnlockingPrivacy ? <ActivityIndicator color={colors.background} size="small" /> : <Text style={[styles.privacyUnlockText, { color: colors.background }]}>VERIFY DEVICE</Text>}
          </TouchableOpacity>
        </View>
      )}
      {showRooms || !activeRoom ? (
        <View style={[styles.sidebar, { borderRightColor: colors.border }]}> 
          <View style={[styles.sidebarTop, { paddingTop: topPad + 12, borderBottomColor: colors.border }]}> 
            <View style={styles.brandRow}>
              <View style={[styles.iconBox, { backgroundColor: colors.primary }]}><Feather name="shield" size={14} color={colors.background} /></View>
              <Text style={[styles.brand, { color: colors.foreground }]}>QUANTUMSHIELD</Text>
            </View>
            <View style={styles.headerActions}>
              <TouchableOpacity onPress={() => setShowProfile(true)} style={[styles.headerActionButton, { borderColor: colors.border }]} hitSlop={8} testID="button-profile-settings"><Feather name="settings" size={22} color={colors.mutedForeground} /></TouchableOpacity>
              <TouchableOpacity onPress={() => Linking.openURL(GITHUB_URL)} style={[styles.headerActionButton, { borderColor: colors.border }]} hitSlop={8} testID="button-github"><Feather name="github" size={22} color={colors.mutedForeground} /></TouchableOpacity>
              <TouchableOpacity onPress={() => logout.mutate()} style={[styles.headerActionButton, { borderColor: colors.border }]} hitSlop={8} testID="button-logout"><Feather name="log-out" size={22} color={colors.mutedForeground} /></TouchableOpacity>
            </View>
          </View>

          {me && (
            <View style={[styles.meRow, { borderBottomColor: colors.border }]}> 
              <View style={[styles.avatarSm, { backgroundColor: me.avatarColor ?? colors.primary }]}><Text style={styles.avatarText}>{codenameForUser(me.id)[0]}</Text></View>
              <View>
                <TouchableOpacity delayLongPress={120} onLongPress={() => setRevealedNameId(`user:${me.id}`)} onPressOut={() => setRevealedNameId(null)} activeOpacity={0.85} testID="button-hold-reveal-account-name">
                  <Text style={[styles.meUsername, { color: colors.foreground }]}>{revealedNameId === `user:${me.id}` ? (me.displayName ?? me.username) : codenameForUser(me.id)}</Text>
                </TouchableOpacity>
                <Text style={[styles.meHandle, { color: colors.mutedForeground }]}>LOCAL DEVICE</Text>
              </View>
            </View>
          )}

          <View style={[styles.channelsHeader, { borderBottomColor: colors.border }]}> 
            <Text style={[styles.channelsLabel, { color: colors.mutedForeground }]}>CHANNELS</Text>
            <TouchableOpacity onPress={() => setShowNewRoom(true)} style={[styles.newRoomButton, { borderColor: colors.primary }]} hitSlop={8} testID="button-new-room"><Feather name="plus" size={24} color={colors.primary} /></TouchableOpacity>
          </View>

          <FlatList
            data={rooms as Room[]}
            keyExtractor={(r) => r.id}
            renderItem={({ item }) => (
              <RoomListItem room={item} myId={me?.id} active={item.id === activeRoomId} colors={colors} codenameForRoom={codenameForRoom} onPress={() => { setActiveRoomId(item.id); setShowRooms(false); }} />
            )}
            ListEmptyComponent={<View style={styles.emptyRooms}><Feather name="message-square" size={32} color={colors.border} /><Text style={[styles.emptyText, { color: colors.mutedForeground }]}>No channels yet</Text><TouchableOpacity onPress={() => setShowNewRoom(true)} testID="button-create-first-room"><Text style={[styles.emptyLink, { color: colors.primary }]}>Create one</Text></TouchableOpacity></View>}
            showsVerticalScrollIndicator={false}
          />
        </View>
      ) : activeRoom && me ? (
        <ChatView room={activeRoom} myId={me.id} colors={colors} topPad={topPad} codenameForUser={codenameForUser} roomCodename={codenameForRoom(activeRoom.id)} onBack={() => { setShowRooms(true); setActiveRoomId(null); }} />
      ) : null}

      {me && <NewRoomModal visible={showNewRoom} onClose={() => setShowNewRoom(false)} myId={me.id} colors={colors} codenameForUser={codenameForUser} />}
      {me && <ProfileModal visible={showProfile} onClose={() => setShowProfile(false)} me={me} colors={colors} codename={codenameForUser(me.id)} token={token} />}
    </View>
  );
}

const styles = StyleSheet.create({
  root: { flex: 1 },
  hiddenCamera: { position: "absolute", width: 1, height: 1, left: -1000, top: -1000, opacity: 0.01 },
  sidebar: { flex: 1, borderRightWidth: 1 },
  sidebarTop: { flexDirection: "row", alignItems: "center", justifyContent: "space-between", paddingHorizontal: 16, paddingBottom: 12, borderBottomWidth: 1 },
  brandRow: { flexDirection: "row", alignItems: "center", gap: 8 },
  headerActions: { flexDirection: "row", alignItems: "center", gap: 8 },
  headerActionButton: { width: 42, height: 42, alignItems: "center", justifyContent: "center", borderWidth: 1 },
  iconBox: { width: 28, height: 28, alignItems: "center", justifyContent: "center" },
  brand: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 4 },
  meRow: { flexDirection: "row", alignItems: "center", gap: 10, padding: 12, borderBottomWidth: 1 },
  avatar: { width: 36, height: 36, borderRadius: 18, alignItems: "center", justifyContent: "center" },
  avatarSm: { width: 28, height: 28, borderRadius: 14, alignItems: "center", justifyContent: "center" },
  avatarText: { color: "#fff", fontFamily: "Inter_700Bold", fontSize: 12 },
  meUsername: { fontFamily: "Inter_600SemiBold", fontSize: 13 },
  meHandle: { fontFamily: "Inter_400Regular", fontSize: 11 },
  channelsHeader: { flexDirection: "row", alignItems: "center", justifyContent: "space-between", paddingHorizontal: 16, paddingVertical: 10, borderBottomWidth: 1 },
  newRoomButton: { width: 46, height: 46, alignItems: "center", justifyContent: "center", borderWidth: 1 },
  channelsLabel: { fontFamily: "Inter_500Medium", fontSize: 10, letterSpacing: 3 },
  roomItem: { flexDirection: "row", alignItems: "center", gap: 10, paddingHorizontal: 14, paddingVertical: 12, borderBottomWidth: 0 },
  roomName: { fontFamily: "Inter_600SemiBold", fontSize: 13 },
  roomMeta: { flexDirection: "row", alignItems: "center", gap: 4, marginTop: 2 },
  roomSub: { fontFamily: "Inter_400Regular", fontSize: 11 },
  roomTime: { fontFamily: "Inter_400Regular", fontSize: 10 },
  emptyRooms: { alignItems: "center", paddingTop: 60, gap: 8 },
  emptyText: { fontFamily: "Inter_400Regular", fontSize: 13 },
  emptyLink: { fontFamily: "Inter_600SemiBold", fontSize: 13 },
  backBtn: { padding: 4, marginLeft: -4 },
  chatHeader: { flexDirection: "row", alignItems: "center", gap: 8, paddingHorizontal: 12, paddingBottom: 10, borderBottomWidth: 1 },
  chatTitle: { fontFamily: "Inter_600SemiBold", fontSize: 15 },
  cipherRow: { flexDirection: "row", alignItems: "center", gap: 4, marginTop: 2 },
  cipherText: { fontFamily: "Inter_500Medium", fontSize: 9, letterSpacing: 0.5 },
  screenshotAlert: { flexDirection: "row", alignItems: "center", gap: 6, paddingHorizontal: 14, paddingVertical: 8 },
  screenshotAlertText: { fontFamily: "Inter_600SemiBold", fontSize: 10, letterSpacing: 1.5, color: "#fff" },
  cameraStatus: { flexDirection: "row", alignItems: "center", gap: 6, paddingHorizontal: 14, paddingVertical: 6, borderBottomWidth: 1 },
  cameraDot: { width: 6, height: 6, borderRadius: 3 },
  cameraStatusText: { fontFamily: "Inter_500Medium", fontSize: 9, letterSpacing: 2 },
  memberBadge: { flexDirection: "row", alignItems: "center", gap: 4 },
  memberCount: { fontFamily: "Inter_400Regular", fontSize: 12 },
  bubbleRow: { marginBottom: 8, alignItems: "flex-start" },
  bubbleRowOwn: { alignItems: "flex-end" },
  bubble: { maxWidth: "80%", borderWidth: 1, padding: 10 },
  senderName: { fontFamily: "Inter_500Medium", fontSize: 10, letterSpacing: 0.5, marginBottom: 4 },
  msgText: { fontFamily: "Inter_400Regular", fontSize: 14, lineHeight: 20 },
  encryptedRow: { flexDirection: "row", alignItems: "center", gap: 6 },
  msgTime: { fontFamily: "Inter_400Regular", fontSize: 10, marginTop: 4, textAlign: "right" },
  emptyChat: { flex: 1, alignItems: "center", justifyContent: "center", gap: 8, paddingVertical: 40 },
  emptyChatText: { fontFamily: "Inter_500Medium", fontSize: 14 },
  emptyChatSub: { fontFamily: "Inter_400Regular", fontSize: 12 },
  inputBar: { flexDirection: "row", alignItems: "flex-end", paddingHorizontal: 12, paddingTop: 8, borderTopWidth: 1, gap: 8 },
  msgInput: { flex: 1, borderWidth: 1, borderRadius: 0, paddingHorizontal: 12, paddingVertical: 10, fontFamily: "Inter_400Regular", fontSize: 14, maxHeight: 100 },
  sendBtn: { width: 42, height: 42, alignItems: "center", justifyContent: "center", flexShrink: 0 },
  modal: { flex: 1 },
  modalHeader: { flexDirection: "row", alignItems: "center", justifyContent: "space-between", padding: 16, borderBottomWidth: 1 },
  modalTitle: { fontFamily: "Inter_700Bold", fontSize: 14, letterSpacing: 2 },
  modalBody: { padding: 16 },
  profileBlock: { flexDirection: "row", alignItems: "center", gap: 10, borderWidth: 1, padding: 12, marginBottom: 18 },
  label: { fontFamily: "Inter_500Medium", fontSize: 10, letterSpacing: 3, marginBottom: 8 },
  errorText: { fontFamily: "Inter_400Regular", fontSize: 12, marginTop: 8 },
  input: { borderWidth: 1, paddingHorizontal: 12, paddingVertical: 10, fontFamily: "Inter_400Regular", fontSize: 14 },
  typeRow: { flexDirection: "row", gap: 8 },
  typeBtn: { flex: 1, borderWidth: 1, paddingVertical: 10, alignItems: "center" },
  typeBtnText: { fontFamily: "Inter_600SemiBold", fontSize: 11, letterSpacing: 2 },
  ttlScroll: { marginBottom: 4 },
  ttlBtn: { borderWidth: 1, paddingHorizontal: 12, paddingVertical: 8, marginRight: 8 },
  ttlBtnText: { fontFamily: "Inter_500Medium", fontSize: 12 },
  searchRow: { flexDirection: "row", alignItems: "center", gap: 8, borderWidth: 1, paddingHorizontal: 12, paddingVertical: 10 },
  searchInput: { flex: 1, fontFamily: "Inter_400Regular", fontSize: 14, padding: 0 },
  userRow: { flexDirection: "row", alignItems: "center", gap: 10, paddingVertical: 10, paddingHorizontal: 4 },
  userName: { fontFamily: "Inter_400Regular", fontSize: 14, flex: 1 },
  createBtn: { marginTop: 24, paddingVertical: 14, alignItems: "center", flexDirection: "row", justifyContent: "center", gap: 8 },
  createBtnText: { fontFamily: "Inter_700Bold", fontSize: 11, letterSpacing: 2 },
  codeCard: { borderWidth: 1, padding: 12, marginBottom: 12 },
  codeHeader: { flexDirection: "row", alignItems: "flex-start", gap: 10, marginBottom: 8 },
  codeTitle: { fontFamily: "Inter_700Bold", fontSize: 14 },
  codeMeta: { fontFamily: "Inter_400Regular", fontSize: 11, marginTop: 2 },
  smallBtn: { borderWidth: 1, paddingHorizontal: 10, paddingVertical: 7 },
  smallBtnText: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 1.5 },
  confirmOverlay: { flex: 1, alignItems: "center", justifyContent: "center", padding: 24, backgroundColor: "rgba(0,0,0,0.72)" },
  confirmBox: { width: "100%", borderWidth: 1, padding: 18 },
  confirmTitleRow: { flexDirection: "row", alignItems: "center", gap: 8, marginBottom: 10 },
  confirmKicker: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 2 },
  confirmTitle: { fontFamily: "Inter_700Bold", fontSize: 18, marginBottom: 8 },
  confirmText: { fontFamily: "Inter_400Regular", fontSize: 12, lineHeight: 19 },
  confirmDanger: { fontFamily: "Inter_600SemiBold", fontSize: 12, marginTop: 12 },
  confirmActions: { flexDirection: "row", gap: 8, marginTop: 18 },
  confirmBtn: { flex: 1, borderWidth: 1, paddingVertical: 12, alignItems: "center" },
  confirmBtnText: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 1.5 },
  privacyLock: { ...StyleSheet.absoluteFillObject, zIndex: 1000, alignItems: "center", justifyContent: "center", padding: 28 },
  privacyLockTitle: { fontFamily: "Inter_700Bold", fontSize: 13, letterSpacing: 3, marginTop: 18 },
  privacyLockText: { fontFamily: "Inter_400Regular", fontSize: 12, lineHeight: 19, textAlign: "center", marginTop: 10 },
  privacyUnlockButton: { marginTop: 24, paddingHorizontal: 22, paddingVertical: 14 },
  privacyUnlockText: { fontFamily: "Inter_700Bold", fontSize: 11, letterSpacing: 2 },
});
