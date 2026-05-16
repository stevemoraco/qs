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
} from "react-native";
import { useSafeAreaInsets } from "react-native-safe-area-context";
import { useRouter } from "expo-router";
import { Feather } from "@expo/vector-icons";
import { KeyboardAvoidingView } from "react-native-keyboard-controller";
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
  useGetUsersSearch,
} from "@workspace/api-client-react";

const CIPHER_SUITE = "AES-256-GCM+ML-KEM-1024+ML-DSA-87";

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
};

function getRoomLabel(room: Room, myId?: string): string {
  if (room.name) return room.name;
  if (room.type === "direct" && room.members) {
    const other = room.members.find((m) => m.id !== myId);
    return other?.displayName ?? other?.username ?? "Direct";
  }
  return `Group (${room.memberCount})`;
}

function formatTime(iso: string): string {
  return new Date(iso).toLocaleTimeString([], { hour: "2-digit", minute: "2-digit" });
}

const messageKeyStore = new Map<string, CryptoKey>();

async function encryptMsg(text: string): Promise<{ ciphertext: string; nonce: string; key: CryptoKey }> {
  const key = await crypto.subtle.generateKey({ name: "AES-GCM", length: 256 }, true, ["encrypt", "decrypt"]);
  const nonce = crypto.getRandomValues(new Uint8Array(12));
  const encrypted = await crypto.subtle.encrypt({ name: "AES-GCM", iv: nonce }, key, new TextEncoder().encode(text));
  const ciphertext = btoa(String.fromCharCode(...new Uint8Array(encrypted)));
  const nonceB64 = btoa(String.fromCharCode(...nonce));
  return { ciphertext, nonce: nonceB64, key };
}

async function decryptMsg(ciphertext: string, nonce: string, key: CryptoKey): Promise<string> {
  const ctBytes = Uint8Array.from(atob(ciphertext), (c) => c.charCodeAt(0));
  const ivBytes = Uint8Array.from(atob(nonce), (c) => c.charCodeAt(0));
  const dec = await crypto.subtle.decrypt({ name: "AES-GCM", iv: ivBytes }, key, ctBytes);
  return new TextDecoder().decode(dec);
}

function RoomListItem({ room, myId, active, onPress, colors }: {
  room: Room;
  myId?: string;
  active: boolean;
  onPress: () => void;
  colors: ReturnType<typeof useColors>;
}) {
  const label = getRoomLabel(room, myId);
  const initial = label[0]?.toUpperCase() ?? "?";
  const avatarColor = room.members?.find((m) => m.id !== myId)?.avatarColor ?? colors.primary;

  return (
    <TouchableOpacity
      onPress={onPress}
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
            <Text style={[styles.roomSub, { color: colors.primary }]}>
              · TTL
            </Text>
          )}
        </View>
      </View>
      {room.lastMessageAt && (
        <Text style={[styles.roomTime, { color: colors.mutedForeground }]}>
          {formatTime(room.lastMessageAt)}
        </Text>
      )}
    </TouchableOpacity>
  );
}

function MessageBubble({ msg, isOwn, colors, plaintext }: {
  msg: Message;
  isOwn: boolean;
  colors: ReturnType<typeof useColors>;
  plaintext?: string;
}) {
  const expired = msg.expiresAt ? new Date(msg.expiresAt).getTime() < Date.now() : false;

  return (
    <View style={[styles.bubbleRow, isOwn && styles.bubbleRowOwn]}>
      <View style={[
        styles.bubble,
        { borderColor: colors.border },
        isOwn ? { backgroundColor: `${colors.primary}20`, borderColor: `${colors.primary}40` } : { backgroundColor: colors.card },
      ]}>
        {!isOwn && (
          <Text style={[styles.senderName, { color: colors.primary }]}>{msg.senderUsername}</Text>
        )}
        {expired ? (
          <Text style={[styles.msgText, { color: colors.mutedForeground, fontStyle: "italic" }]}>
            Message expired — key destroyed
          </Text>
        ) : plaintext ? (
          <Text style={[styles.msgText, { color: colors.foreground }]}>{plaintext}</Text>
        ) : (
          <View style={styles.encryptedRow}>
            <Feather name="lock" size={12} color={colors.mutedForeground} />
            <Text style={[styles.msgText, { color: colors.mutedForeground }]}>Encrypted</Text>
          </View>
        )}
        <Text style={[styles.msgTime, { color: colors.mutedForeground }]}>
          {formatTime(msg.createdAt)}
        </Text>
      </View>
    </View>
  );
}

function ChatView({ room, myId, colors }: { room: Room; myId: string; colors: ReturnType<typeof useColors> }) {
  const qc = useQueryClient();
  const [input, setInput] = useState("");
  const [decrypted, setDecrypted] = useState<Record<string, string>>({});
  const insets = useSafeAreaInsets();

  const { data: messages = [] } = useGetRoomsRoomIdMessages(
    room.id, {},
    { query: { queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id), refetchInterval: 3000 } }
  );

  const { data: members = [] } = useGetRoomsRoomIdMembers(room.id, {
    query: { queryKey: getGetRoomsRoomIdMembersQueryKey(room.id) },
  });

  const sendMsg = usePostRoomsRoomIdMessages(room.id, {
    mutation: {
      onSuccess: () => qc.invalidateQueries({ queryKey: getGetRoomsRoomIdMessagesQueryKey(room.id) }),
    },
  });

  const handleSend = async () => {
    const text = input.trim();
    if (!text) return;
    setInput("");
    const { ciphertext, nonce, key } = await encryptMsg(text);
    sendMsg.mutate(
      { data: { ciphertext, nonce, algorithm: CIPHER_SUITE, ttlSeconds: room.ttlSeconds } },
      {
        onSuccess: (msg) => {
          messageKeyStore.set(msg.id, key);
          decryptMsg(msg.ciphertext, msg.nonce, key)
            .then((pt) => setDecrypted((d) => ({ ...d, [msg.id]: pt })))
            .catch(() => {});
        },
      }
    );
  };

  const reversed = [...messages].reverse();

  return (
    <KeyboardAvoidingView style={{ flex: 1 }} behavior="padding" keyboardVerticalOffset={0}>
      <View style={[styles.chatHeader, { borderBottomColor: colors.border }]}>
        <View>
          <Text style={[styles.chatTitle, { color: colors.foreground }]} numberOfLines={1}>
            {getRoomLabel(room, myId)}
          </Text>
          <View style={styles.cipherRow}>
            <Feather name="shield" size={10} color={colors.primary} />
            <Text style={[styles.cipherText, { color: colors.primary }]}>{CIPHER_SUITE}</Text>
          </View>
        </View>
        <View style={styles.memberBadge}>
          <Feather name="users" size={12} color={colors.mutedForeground} />
          <Text style={[styles.memberCount, { color: colors.mutedForeground }]}>{members.length}</Text>
        </View>
      </View>

      <FlatList
        data={reversed}
        keyExtractor={(m) => m.id}
        inverted
        contentContainerStyle={{ padding: 16 }}
        renderItem={({ item }) => (
          <MessageBubble
            msg={item as Message}
            isOwn={item.senderId === myId}
            colors={colors}
            plaintext={decrypted[item.id]}
          />
        )}
        ListEmptyComponent={
          <View style={styles.emptyChat}>
            <Feather name="lock" size={40} color={colors.border} />
            <Text style={[styles.emptyChatText, { color: colors.mutedForeground }]}>
              No messages yet
            </Text>
            <Text style={[styles.emptyChatSub, { color: colors.mutedForeground }]}>
              All messages are end-to-end encrypted
            </Text>
          </View>
        }
        keyboardShouldPersistTaps="handled"
        keyboardDismissMode="interactive"
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
        <TouchableOpacity
          onPress={handleSend}
          disabled={!input.trim() || sendMsg.isPending}
          style={[styles.sendBtn, { backgroundColor: colors.primary }, (!input.trim() || sendMsg.isPending) && { opacity: 0.4 }]}
          testID="button-send"
        >
          <Feather name="send" size={16} color={colors.background} />
        </TouchableOpacity>
      </View>
    </KeyboardAvoidingView>
  );
}

function NewRoomModal({ visible, onClose, myId, colors }: {
  visible: boolean;
  onClose: () => void;
  myId: string;
  colors: ReturnType<typeof useColors>;
}) {
  const qc = useQueryClient();
  const [name, setName] = useState("");
  const [type, setType] = useState<"direct" | "group">("direct");
  const [ttl, setTtl] = useState<number | null>(null);
  const [search, setSearch] = useState("");
  const [selected, setSelected] = useState<string[]>([]);

  const { data: results = [] } = useGetUsersSearch(
    { q: search },
    { query: { enabled: search.length > 0 } }
  );

  const createRoom = usePostRooms({
    mutation: {
      onSuccess: () => {
        qc.invalidateQueries({ queryKey: getGetRoomsQueryKey() });
        onClose();
        setName(""); setSearch(""); setSelected([]);
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
          <TouchableOpacity onPress={onClose} testID="button-close-dialog">
            <Feather name="x" size={20} color={colors.mutedForeground} />
          </TouchableOpacity>
        </View>

        <ScrollView contentContainerStyle={styles.modalBody} keyboardShouldPersistTaps="handled">
          <Text style={[styles.label, { color: colors.mutedForeground }]}>CHANNEL NAME</Text>
          <TextInput
            style={[styles.input, { backgroundColor: colors.card, borderColor: colors.border, color: colors.foreground }]}
            value={name}
            onChangeText={setName}
            placeholder="Optional name..."
            placeholderTextColor={colors.mutedForeground}
            testID="input-room-name"
          />

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>TYPE</Text>
          <View style={styles.typeRow}>
            {(["direct", "group"] as const).map((t) => (
              <TouchableOpacity
                key={t}
                onPress={() => setType(t)}
                style={[
                  styles.typeBtn,
                  { borderColor: type === t ? colors.primary : colors.border },
                  type === t && { backgroundColor: `${colors.primary}20` },
                ]}
                testID={`button-type-${t}`}
              >
                <Text style={[styles.typeBtnText, { color: type === t ? colors.primary : colors.mutedForeground }]}>
                  {t.toUpperCase()}
                </Text>
              </TouchableOpacity>
            ))}
          </View>

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>MESSAGE EXPIRY (TTL)</Text>
          <ScrollView horizontal showsHorizontalScrollIndicator={false} style={styles.ttlScroll}>
            {TTL_OPTIONS.map((o) => (
              <TouchableOpacity
                key={String(o.v)}
                onPress={() => setTtl(o.v)}
                style={[
                  styles.ttlBtn,
                  { borderColor: ttl === o.v ? colors.primary : colors.border },
                  ttl === o.v && { backgroundColor: `${colors.primary}20` },
                ]}
              >
                <Text style={[styles.ttlBtnText, { color: ttl === o.v ? colors.primary : colors.mutedForeground }]}>
                  {o.label}
                </Text>
              </TouchableOpacity>
            ))}
          </ScrollView>

          <Text style={[styles.label, { color: colors.mutedForeground, marginTop: 16 }]}>ADD MEMBERS</Text>
          <View style={[styles.searchRow, { backgroundColor: colors.card, borderColor: colors.border }]}>
            <Feather name="search" size={14} color={colors.mutedForeground} />
            <TextInput
              style={[styles.searchInput, { color: colors.foreground }]}
              value={search}
              onChangeText={setSearch}
              placeholder="Search username..."
              placeholderTextColor={colors.mutedForeground}
              autoCapitalize="none"
              testID="input-search-users"
            />
          </View>

          {results.filter((u) => u.id !== myId).map((u) => (
            <TouchableOpacity
              key={u.id}
              onPress={() => setSelected((s) => s.includes(u.id) ? s.filter((x) => x !== u.id) : [...s, u.id])}
              style={[styles.userRow, selected.includes(u.id) && { backgroundColor: `${colors.primary}15` }]}
              testID={`button-user-${u.id}`}
            >
              <View style={[styles.avatarSm, { backgroundColor: u.avatarColor ?? colors.primary }]}>
                <Text style={styles.avatarText}>{u.username[0].toUpperCase()}</Text>
              </View>
              <Text style={[styles.userName, { color: colors.foreground }]}>
                {u.displayName ?? u.username}
              </Text>
              {selected.includes(u.id) && (
                <Feather name="check-circle" size={16} color={colors.primary} />
              )}
            </TouchableOpacity>
          ))}

          <TouchableOpacity
            style={[styles.createBtn, { backgroundColor: colors.primary }, createRoom.isPending && { opacity: 0.5 }]}
            onPress={() => createRoom.mutate({ data: { name: name || null, type, memberIds: selected, ttlSeconds: ttl } })}
            disabled={createRoom.isPending}
            testID="button-create-room"
          >
            {createRoom.isPending ? (
              <ActivityIndicator color={colors.background} size="small" />
            ) : (
              <Text style={[styles.createBtnText, { color: colors.background }]}>
                CREATE ENCRYPTED CHANNEL
              </Text>
            )}
          </TouchableOpacity>
        </ScrollView>
      </View>
    </Modal>
  );
}

export default function AppScreen() {
  const colors = useColors();
  const insets = useSafeAreaInsets();
  const router = useRouter();
  const qc = useQueryClient();
  const { clearAuth } = useAuth();

  const [activeRoomId, setActiveRoomId] = useState<string | null>(null);
  const [showNewRoom, setShowNewRoom] = useState(false);
  const [showRooms, setShowRooms] = useState(true);

  const { data: me } = useGetAuthMe();
  const { data: rooms = [] } = useGetRooms({
    query: { queryKey: getGetRoomsQueryKey(), refetchInterval: 5000 },
  });

  const logout = usePostAuthLogout({
    mutation: {
      onSuccess: async () => {
        await clearAuth();
        router.replace("/login");
      },
    },
  });

  const activeRoom = rooms.find((r) => r.id === activeRoomId) as Room | undefined;

  const topPad = Platform.OS === "web" ? 67 : insets.top;

  return (
    <View style={[styles.root, { backgroundColor: colors.background }]}>
      {showRooms || !activeRoom ? (
        <View style={[styles.sidebar, { borderRightColor: colors.border }]}>
          <View style={[styles.sidebarTop, { paddingTop: topPad + 12, borderBottomColor: colors.border }]}>
            <View style={styles.brandRow}>
              <View style={[styles.iconBox, { backgroundColor: colors.primary }]}>
                <Feather name="shield" size={14} color={colors.background} />
              </View>
              <Text style={[styles.brand, { color: colors.foreground }]}>QUANTUMSHIELD</Text>
            </View>
            <TouchableOpacity onPress={() => logout.mutate({})} testID="button-logout">
              <Feather name="log-out" size={18} color={colors.mutedForeground} />
            </TouchableOpacity>
          </View>

          {me && (
            <View style={[styles.meRow, { borderBottomColor: colors.border }]}>
              <View style={[styles.avatarSm, { backgroundColor: me.avatarColor ?? colors.primary }]}>
                <Text style={styles.avatarText}>{me.username[0].toUpperCase()}</Text>
              </View>
              <View>
                <Text style={[styles.meUsername, { color: colors.foreground }]}>
                  {me.displayName ?? me.username}
                </Text>
                <Text style={[styles.meHandle, { color: colors.mutedForeground }]}>@{me.username}</Text>
              </View>
            </View>
          )}

          <View style={[styles.channelsHeader, { borderBottomColor: colors.border }]}>
            <Text style={[styles.channelsLabel, { color: colors.mutedForeground }]}>CHANNELS</Text>
            <TouchableOpacity onPress={() => setShowNewRoom(true)} testID="button-new-room">
              <Feather name="plus" size={18} color={colors.primary} />
            </TouchableOpacity>
          </View>

          <FlatList
            data={rooms as Room[]}
            keyExtractor={(r) => r.id}
            renderItem={({ item }) => (
              <RoomListItem
                room={item}
                myId={me?.id}
                active={item.id === activeRoomId}
                colors={colors}
                onPress={() => {
                  setActiveRoomId(item.id);
                  setShowRooms(false);
                }}
              />
            )}
            ListEmptyComponent={
              <View style={styles.emptyRooms}>
                <Feather name="message-square" size={32} color={colors.border} />
                <Text style={[styles.emptyText, { color: colors.mutedForeground }]}>No channels yet</Text>
                <TouchableOpacity onPress={() => setShowNewRoom(true)} testID="button-create-first-room">
                  <Text style={[styles.emptyLink, { color: colors.primary }]}>Create one</Text>
                </TouchableOpacity>
              </View>
            }
            showsVerticalScrollIndicator={false}
          />
        </View>
      ) : activeRoom && me ? (
        <View style={{ flex: 1 }}>
          <View style={[styles.chatTopBar, { paddingTop: topPad + 8, borderBottomColor: colors.border }]}>
            <TouchableOpacity onPress={() => { setShowRooms(true); setActiveRoomId(null); }} style={styles.backBtn}>
              <Feather name="chevron-left" size={22} color={colors.primary} />
            </TouchableOpacity>
            <Text style={[styles.chatTopTitle, { color: colors.foreground }]} numberOfLines={1}>
              {getRoomLabel(activeRoom, me.id)}
            </Text>
          </View>
          <ChatView room={activeRoom} myId={me.id} colors={colors} />
        </View>
      ) : null}

      {me && (
        <NewRoomModal
          visible={showNewRoom}
          onClose={() => setShowNewRoom(false)}
          myId={me.id}
          colors={colors}
        />
      )}
    </View>
  );
}

const styles = StyleSheet.create({
  root: { flex: 1 },
  sidebar: { flex: 1, borderRightWidth: 1 },
  sidebarTop: { flexDirection: "row", alignItems: "center", justifyContent: "space-between", paddingHorizontal: 16, paddingBottom: 12, borderBottomWidth: 1 },
  brandRow: { flexDirection: "row", alignItems: "center", gap: 8 },
  iconBox: { width: 28, height: 28, alignItems: "center", justifyContent: "center" },
  brand: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 4 },
  meRow: { flexDirection: "row", alignItems: "center", gap: 10, padding: 12, borderBottomWidth: 1 },
  avatar: { width: 36, height: 36, borderRadius: 18, alignItems: "center", justifyContent: "center" },
  avatarSm: { width: 28, height: 28, borderRadius: 14, alignItems: "center", justifyContent: "center" },
  avatarText: { color: "#fff", fontFamily: "Inter_700Bold", fontSize: 12 },
  meUsername: { fontFamily: "Inter_600SemiBold", fontSize: 13 },
  meHandle: { fontFamily: "Inter_400Regular", fontSize: 11 },
  channelsHeader: { flexDirection: "row", alignItems: "center", justifyContent: "space-between", paddingHorizontal: 16, paddingVertical: 10, borderBottomWidth: 1 },
  channelsLabel: { fontFamily: "Inter_500Medium", fontSize: 10, letterSpacing: 3 },
  roomItem: { flexDirection: "row", alignItems: "center", gap: 10, paddingHorizontal: 14, paddingVertical: 12, borderBottomWidth: 0 },
  roomName: { fontFamily: "Inter_600SemiBold", fontSize: 13 },
  roomMeta: { flexDirection: "row", alignItems: "center", gap: 4, marginTop: 2 },
  roomSub: { fontFamily: "Inter_400Regular", fontSize: 11 },
  roomTime: { fontFamily: "Inter_400Regular", fontSize: 10 },
  emptyRooms: { alignItems: "center", paddingTop: 60, gap: 8 },
  emptyText: { fontFamily: "Inter_400Regular", fontSize: 13 },
  emptyLink: { fontFamily: "Inter_600SemiBold", fontSize: 13 },
  chatTopBar: { flexDirection: "row", alignItems: "center", paddingHorizontal: 12, paddingBottom: 8, borderBottomWidth: 1, gap: 8 },
  backBtn: { padding: 4 },
  chatTopTitle: { fontFamily: "Inter_600SemiBold", fontSize: 16, flex: 1 },
  chatHeader: { flexDirection: "row", alignItems: "center", justifyContent: "space-between", paddingHorizontal: 16, paddingVertical: 10, borderBottomWidth: 1 },
  chatTitle: { fontFamily: "Inter_600SemiBold", fontSize: 15 },
  cipherRow: { flexDirection: "row", alignItems: "center", gap: 4, marginTop: 2 },
  cipherText: { fontFamily: "Inter_500Medium", fontSize: 9, letterSpacing: 0.5 },
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
  label: { fontFamily: "Inter_500Medium", fontSize: 10, letterSpacing: 3, marginBottom: 8 },
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
});
