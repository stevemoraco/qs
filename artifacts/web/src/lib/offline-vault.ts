export type OfflineRoom = {
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

export type RecipientEncryptedKeyValue = string | string[];
export type RecipientEncryptedKeys = Record<string, RecipientEncryptedKeyValue>;

export type OfflineMessage = {
  id: string;
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
};

export type OfflineMember = {
  id: string;
  username: string;
  displayName?: string | null;
  avatarColor?: string | null;
};

export type OfflineKeyBundle = {
  userId: string;
  kemPublicKey?: string | null;
  dsaPublicKey?: string | null;
  kemSignature?: string | null;
  trustedAt: string;
};

export type OfflineOutboxEntry = {
  id: string;
  roomId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  signature: string;
  senderDsaPublicKey?: string | null;
  recipientEncryptedKeys: RecipientEncryptedKeys;
  ttlSeconds?: number | null;
  createdAt: string;
  availableAt?: string | null;
};

const DB_NAME = "quantumshield-offline-vault";
const DB_VERSION = 1;
const ROOMS_STORE = "rooms";
const MESSAGES_STORE = "messages";
const MEMBERS_STORE = "members";
const KEY_BUNDLES_STORE = "keyBundles";
const OUTBOX_STORE = "outbox";

function openDb(): Promise<IDBDatabase | null> {
  if (typeof indexedDB === "undefined") return Promise.resolve(null);
  return new Promise((resolve) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);
    req.onupgradeneeded = () => {
      const db = req.result;
      if (!db.objectStoreNames.contains(ROOMS_STORE)) db.createObjectStore(ROOMS_STORE, { keyPath: "id" });
      if (!db.objectStoreNames.contains(MESSAGES_STORE)) db.createObjectStore(MESSAGES_STORE, { keyPath: "id" });
      if (!db.objectStoreNames.contains(MEMBERS_STORE)) db.createObjectStore(MEMBERS_STORE, { keyPath: "roomId" });
      if (!db.objectStoreNames.contains(KEY_BUNDLES_STORE)) db.createObjectStore(KEY_BUNDLES_STORE, { keyPath: "userId" });
      if (!db.objectStoreNames.contains(OUTBOX_STORE)) db.createObjectStore(OUTBOX_STORE, { keyPath: "id" });
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => resolve(null);
  });
}

async function withStore<T>(
  storeName: string,
  mode: IDBTransactionMode,
  fn: (store: IDBObjectStore) => void,
  fallback: T,
): Promise<T> {
  const db = await openDb();
  if (!db) return fallback;
  return new Promise<T>((resolve) => {
    const tx = db.transaction(storeName, mode);
    let settled = false;
    const finish = (value: T) => {
      if (settled) return;
      settled = true;
      db.close();
      resolve(value);
    };
    tx.oncomplete = () => finish(fallback);
    tx.onerror = () => finish(fallback);
    tx.onabort = () => finish(fallback);
    fn(tx.objectStore(storeName));
  });
}

function getAll<T>(storeName: string): Promise<T[]> {
  return openDb().then((db) => {
    if (!db) return [];
    return new Promise<T[]>((resolve) => {
      let settled = false;
      const finish = (value: T[]) => {
        if (settled) return;
        settled = true;
        db.close();
        resolve(value);
      };
      const tx = db.transaction(storeName, "readonly");
      const req = tx.objectStore(storeName).getAll();
      req.onsuccess = () => finish((req.result ?? []) as T[]);
      req.onerror = () => finish([]);
      tx.onerror = () => finish([]);
      tx.onabort = () => finish([]);
    });
  });
}

export async function cacheRooms(rooms: OfflineRoom[]): Promise<void> {
  const now = Date.now();
  await withStore<void>(ROOMS_STORE, "readwrite", (store) => {
    for (const room of rooms) store.put({ ...room, cachedAt: now });
  }, undefined);
}

export async function getCachedRooms(): Promise<OfflineRoom[]> {
  const rooms = await getAll<OfflineRoom & { cachedAt?: number }>(ROOMS_STORE);
  return rooms.sort((a, b) => (b.lastMessageAt ?? "").localeCompare(a.lastMessageAt ?? "") || (b.cachedAt ?? 0) - (a.cachedAt ?? 0));
}

export async function cacheRoomMessages(roomId: string, messages: OfflineMessage[]): Promise<void> {
  const now = Date.now();
  await withStore<void>(MESSAGES_STORE, "readwrite", (store) => {
    for (const msg of messages) store.put({ ...msg, roomId, cachedAt: now });
  }, undefined);
}

export async function getCachedRoomMessages(roomId: string): Promise<OfflineMessage[]> {
  const messages = await getAll<OfflineMessage & { roomId: string; cachedAt?: number }>(MESSAGES_STORE);
  return messages
    .filter((msg) => msg.roomId === roomId)
    .sort((a, b) => a.createdAt.localeCompare(b.createdAt));
}

export async function cacheRoomMembers(roomId: string, members: OfflineMember[]): Promise<void> {
  await withStore<void>(MEMBERS_STORE, "readwrite", (store) => {
    store.put({ roomId, members, cachedAt: Date.now() });
  }, undefined);
}

export async function getCachedRoomMembers(roomId: string): Promise<OfflineMember[]> {
  const db = await openDb();
  if (!db) return [];
  return new Promise((resolve) => {
    const tx = db.transaction(MEMBERS_STORE, "readonly");
    const req = tx.objectStore(MEMBERS_STORE).get(roomId);
    req.onsuccess = () => resolve(Array.isArray(req.result?.members) ? req.result.members : []);
    req.onerror = () => resolve([]);
    tx.oncomplete = () => db.close();
    tx.onerror = () => db.close();
    tx.onabort = () => db.close();
  });
}

export async function cacheTrustedKeyBundle(bundle: OfflineKeyBundle): Promise<void> {
  await withStore<void>(KEY_BUNDLES_STORE, "readwrite", (store) => {
    store.put(bundle);
  }, undefined);
}

export async function getCachedTrustedKeyBundle(userId: string): Promise<OfflineKeyBundle | null> {
  const db = await openDb();
  if (!db) return null;
  return new Promise((resolve) => {
    const tx = db.transaction(KEY_BUNDLES_STORE, "readonly");
    const req = tx.objectStore(KEY_BUNDLES_STORE).get(userId);
    req.onsuccess = () => resolve((req.result as OfflineKeyBundle | undefined) ?? null);
    req.onerror = () => resolve(null);
    tx.oncomplete = () => db.close();
    tx.onerror = () => db.close();
    tx.onabort = () => db.close();
  });
}

export async function enqueueOutbox(entry: OfflineOutboxEntry): Promise<void> {
  await withStore<void>(OUTBOX_STORE, "readwrite", (store) => {
    store.put(entry);
  }, undefined);
}

export async function getOutboxEntries(): Promise<OfflineOutboxEntry[]> {
  const entries = await getAll<OfflineOutboxEntry>(OUTBOX_STORE);
  return entries.sort((a, b) => a.createdAt.localeCompare(b.createdAt));
}

export async function deleteOutboxEntry(id: string): Promise<void> {
  await withStore<void>(OUTBOX_STORE, "readwrite", (store) => {
    store.delete(id);
  }, undefined);
}

export function createLocalOutboxId(): string {
  return `local-${Date.now().toString(36)}-${crypto.randomUUID?.() ?? Math.random().toString(36).slice(2)}`;
}
