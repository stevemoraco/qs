import { Router } from "express";
import { db, messagesTable, preKeysTable, roomMembersTable, roomsTable, usersTable } from "@workspace/db";
import { eq, and, lt, desc, ne, inArray, isNull, isNotNull, lte, or } from "drizzle-orm";
import { randomInt } from "crypto";
import { ml_dsa87 } from "@noble/post-quantum/ml-dsa.js";
import { PostRoomsRoomIdMessagesBody } from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";
import { enqueuePushNotification, notifyUser } from "./push";
import { logger } from "../lib/logger";
import { createTimeQuorumAttestation, type TimeQuorumAttestation } from "../lib/time-quorum";

const router = Router();
const CIPHER_SUITE = "AES-256-GCM+ML-KEM-1024+ML-DSA-87";
const MAX_MESSAGE_TTL_SECONDS = 35_337_600;
const MAX_DELIVERY_FUZZ_SECONDS = 35_337_600;
const MAX_WRAPPED_KEY_LENGTH = 16_384;
const EXPIRED_KEY_PURGE_INTERVAL_MS = 30_000;
const EXPERIMENTAL_QUORUM_DECAY = "experimental_quorum_decay";

function routeParam(value: string | string[] | undefined): string {
  return Array.isArray(value) ? value[0] : (value ?? "");
}

async function purgeExpiredMessageKeys(attestation?: TimeQuorumAttestation): Promise<void> {
  try {
    const decayAttestation = attestation ?? await createTimeQuorumAttestation();
    const quorumNow = new Date(decayAttestation.synthesizedEpochMs);
    const expiredExperimentalRows = await db
      .select({ id: messagesTable.id })
      .from(messagesTable)
      .innerJoin(roomsTable, eq(messagesTable.roomId, roomsTable.id))
      .where(and(
        lte(messagesTable.expiresAt, quorumNow),
        or(isNotNull(messagesTable.recipientEncryptedKeys), isNull(messagesTable.decayedAt)),
        eq(roomsTable.decayMode, EXPERIMENTAL_QUORUM_DECAY),
      ));

    if (expiredExperimentalRows.length > 0) {
      await db
        .update(messagesTable)
        .set({ recipientEncryptedKeys: null, decayedAt: quorumNow, decayAttestation })
        .where(inArray(messagesTable.id, expiredExperimentalRows.map((row) => row.id)));
    }
  } catch (error) {
    logger.warn({ error }, "Failed to purge expired message keys");
  }
}

const expiredKeyPurgeTimer = setInterval(() => {
  void purgeExpiredMessageKeys();
}, EXPIRED_KEY_PURGE_INTERVAL_MS);
expiredKeyPurgeTimer.unref?.();

function validDurationSeconds(value: number | null | undefined, max: number): boolean {
  if (value === null || value === undefined) return true;
  return Number.isSafeInteger(value) && value >= 0 && value <= max;
}

type RecipientEncryptedKeyValue = string | string[];
type RecipientEncryptedKeys = Record<string, RecipientEncryptedKeyValue>;

function isValidWrappedKeyValue(value: unknown): value is RecipientEncryptedKeyValue {
  if (typeof value === "string") return value.length > 0 && value.length <= MAX_WRAPPED_KEY_LENGTH;
  if (!Array.isArray(value) || value.length === 0 || value.length > 16) return false;
  return value.every((item) => typeof item === "string" && item.length > 0 && item.length <= MAX_WRAPPED_KEY_LENGTH);
}

function isValidRecipientEncryptedKeys(
  value: unknown,
  expectedUserIds: Set<string>,
): value is RecipientEncryptedKeys {
  if (!value || typeof value !== "object" || Array.isArray(value)) return false;
  const keys = Object.entries(value);
  if (keys.length !== expectedUserIds.size) return false;

  for (const [userId, wrappedKey] of keys) {
    if (!expectedUserIds.has(userId)) return false;
    if (!isValidWrappedKeyValue(wrappedKey)) return false;
  }

  return true;
}

function stableJson(value: unknown): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(stableJson).join(",")}]`;
  return `{${Object.keys(value as Record<string, unknown>)
    .sort()
    .map((key) => `${JSON.stringify(key)}:${stableJson((value as Record<string, unknown>)[key])}`)
    .join(",")}}`;
}

function messageSignaturePayload(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys: RecipientEncryptedKeys;
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
      recipientEncryptedKeys: input.recipientEncryptedKeys,
    }),
  );
}

type MessageRow = typeof messagesTable.$inferSelect;

function messageResponse(message: MessageRow) {
  return {
    id: message.id,
    roomId: message.roomId,
    senderId: message.senderId,
    senderUsername: null,
    ciphertext: message.ciphertext,
    nonce: message.nonce,
    algorithm: message.algorithm,
    signature: message.signature,
    senderDsaPublicKey: message.senderDsaPublicKey,
    recipientEncryptedKeys: message.recipientEncryptedKeys,
    decayAttestation: message.decayAttestation,
    decayedAt: message.decayedAt,
    expiresAt: message.expiresAt,
    availableAt: message.availableAt,
    createdAt: message.createdAt,
  };
}

function verifiesMessageSignature(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys: RecipientEncryptedKeys;
  signature: string | null | undefined;
  dsaPublicKey: string | null | undefined;
}): boolean {
  if (!input.signature || !input.dsaPublicKey) return false;
  try {
    return ml_dsa87.verify(
      new Uint8Array(Buffer.from(input.signature, "base64")),
      messageSignaturePayload(input),
      new Uint8Array(Buffer.from(input.dsaPublicKey, "base64")),
    );
  } catch {
    return false;
  }
}

router.get("/rooms/:roomId/messages", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const membership = await db
    .select()
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, req.userId!)))
    .limit(1);

  if (membership.length === 0) {
    res.status(403).json({ error: "Not a member of this room" });
    return;
  }

  const limit = Math.min(Number(req.query.limit ?? 50), 100);
  const before = req.query.before as string | undefined;

  const [room] = await db
    .select({ ttlSeconds: roomsTable.ttlSeconds, ttlMode: roomsTable.ttlMode, decayMode: roomsTable.decayMode })
    .from(roomsTable)
    .where(eq(roomsTable.id, roomId))
    .limit(1);

  const isExperimentalQuorumDecay = room?.decayMode === EXPERIMENTAL_QUORUM_DECAY;
  const readAttestation = isExperimentalQuorumDecay ? await createTimeQuorumAttestation() : null;
  const serverNow = readAttestation ? new Date(readAttestation.synthesizedEpochMs) : new Date();
  if (readAttestation) {
    await purgeExpiredMessageKeys(readAttestation);
  } else {
    void purgeExpiredMessageKeys();
  }

  let query = db
    .select({
      message: messagesTable,
    })
    .from(messagesTable)
    .where(and(
      eq(messagesTable.roomId, roomId),
      or(lte(messagesTable.availableAt, serverNow), eq(messagesTable.senderId, req.userId!)),
    ))
    .orderBy(desc(messagesTable.createdAt))
    .limit(limit);

  if (before) {
    const [beforeMsg] = await db
      .select({ createdAt: messagesTable.createdAt })
      .from(messagesTable)
      .where(and(eq(messagesTable.id, before), eq(messagesTable.roomId, roomId)))
      .limit(1);
    if (beforeMsg) {
      query = db
        .select({
          message: messagesTable,
        })
        .from(messagesTable)
        .where(and(
          eq(messagesTable.roomId, roomId),
          or(lte(messagesTable.availableAt, serverNow), eq(messagesTable.senderId, req.userId!)),
          lt(messagesTable.createdAt, beforeMsg.createdAt),
        ))
        .orderBy(desc(messagesTable.createdAt))
        .limit(limit);
    }
  }

  const rows = await query;

  const visibleRows = isExperimentalQuorumDecay ? rows : rows.filter((r) => !r.message.expiresAt || r.message.expiresAt > serverNow);
  const viewedExpiresAt = room?.ttlSeconds && room.ttlMode === "after_view" ? new Date(serverNow.getTime() + room.ttlSeconds * 1000) : null;
  const firstViewedIds = viewedExpiresAt
    ? visibleRows.filter((r) => !r.message.expiresAt && r.message.senderId !== req.userId).map((r) => r.message.id)
    : [];

  if (firstViewedIds.length > 0) {
    await db
      .update(messagesTable)
      .set({
        expiresAt: viewedExpiresAt,
        ...(readAttestation ? { decayAttestation: readAttestation } : {}),
      })
      .where(and(inArray(messagesTable.id, firstViewedIds), isNull(messagesTable.expiresAt)));
  }

  const messages = visibleRows
    .map((r) => ({
      id: r.message.id,
      roomId: r.message.roomId,
      senderId: r.message.senderId,
      senderUsername: null,
      ciphertext: r.message.ciphertext,
      nonce: r.message.nonce,
      algorithm: r.message.algorithm,
      signature: r.message.signature,
      senderDsaPublicKey: r.message.senderDsaPublicKey,
      recipientEncryptedKeys: r.message.recipientEncryptedKeys,
      decayAttestation: firstViewedIds.includes(r.message.id) && readAttestation ? readAttestation : r.message.decayAttestation,
      decayedAt: r.message.decayedAt,
      expiresAt: r.message.expiresAt ?? (firstViewedIds.includes(r.message.id) ? viewedExpiresAt : null),
      availableAt: r.message.availableAt,
      createdAt: r.message.createdAt,
    }));

  res.json(messages.reverse());
});

router.post("/rooms/:roomId/messages", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const membership = await db
    .select()
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, req.userId!)))
    .limit(1);

  if (membership.length === 0) {
    res.status(403).json({ error: "Not a member of this room" });
    return;
  }

  const parse = PostRoomsRoomIdMessagesBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { ciphertext, nonce, algorithm, signature, recipientEncryptedKeys, ttlSeconds } = parse.data;
  const senderDsaPublicKey = typeof req.body?.senderDsaPublicKey === "string" ? req.body.senderDsaPublicKey : null;
  if (algorithm !== CIPHER_SUITE) {
    res.status(400).json({ error: "Unsupported message algorithm" });
    return;
  }
  if (!validDurationSeconds(ttlSeconds, MAX_MESSAGE_TTL_SECONDS)) {
    res.status(400).json({ error: "Invalid message TTL" });
    return;
  }

  const [room] = await db
    .select({ ttlSeconds: roomsTable.ttlSeconds, ttlMode: roomsTable.ttlMode, deliveryFuzzSeconds: roomsTable.deliveryFuzzSeconds, decayMode: roomsTable.decayMode })
    .from(roomsTable)
    .where(eq(roomsTable.id, roomId))
    .limit(1);

  if (!room || !validDurationSeconds(room.ttlSeconds, MAX_MESSAGE_TTL_SECONDS) || !validDurationSeconds(room.deliveryFuzzSeconds, MAX_DELIVERY_FUZZ_SECONDS)) {
    res.status(400).json({ error: "Invalid room TTL configuration" });
    return;
  }

  const roomMemberRows = await db
    .select({ userId: roomMembersTable.userId })
    .from(roomMembersTable)
    .where(eq(roomMembersTable.roomId, roomId));
  const expectedRecipientIds = new Set(roomMemberRows.map((member) => member.userId));
  if (!isValidRecipientEncryptedKeys(recipientEncryptedKeys, expectedRecipientIds)) {
    res.status(400).json({ error: "recipientEncryptedKeys must include exactly one wrapped key for each current room member" });
    return;
  }
  const [sender] = await db
    .select({ dsaPublicKey: usersTable.dsaPublicKey })
    .from(usersTable)
    .where(eq(usersTable.id, req.userId!))
    .limit(1);
  const senderDsaCandidates = new Set<string>();
  if (sender?.dsaPublicKey) senderDsaCandidates.add(sender.dsaPublicKey);
  if (senderDsaPublicKey) {
    const [historicalSenderKey] = await db
      .select({ dsaPublicKey: preKeysTable.dsaPublicKey })
      .from(preKeysTable)
      .where(and(eq(preKeysTable.userId, req.userId!), eq(preKeysTable.dsaPublicKey, senderDsaPublicKey)))
      .limit(1);
    if (historicalSenderKey?.dsaPublicKey) senderDsaCandidates.add(historicalSenderKey.dsaPublicKey);
    senderDsaCandidates.add(senderDsaPublicKey);
  }
  const verifiedSenderDsaPublicKey = [...senderDsaCandidates].find((candidate) => verifiesMessageSignature({
    roomId,
    senderId: req.userId!,
    ciphertext,
    nonce,
    algorithm,
    recipientEncryptedKeys,
    signature,
    dsaPublicKey: candidate,
  }));
  if (!verifiedSenderDsaPublicKey) {
    res.status(400).json({
      error: "Invalid message signature",
      code: "INVALID_MESSAGE_SIGNATURE",
      details: senderDsaPublicKey
        ? "The authenticated device signing key did not verify this message payload."
        : "No sender device signing key was supplied for this message.",
    });
    return;
  }

  if (senderDsaPublicKey && !senderDsaCandidates.has(senderDsaPublicKey)) {
    logger.warn({ userId: req.userId }, "message accepted with embedded sender signing key not yet present in prekey history");
  }
  if (!verifiesMessageSignature({
      roomId,
      senderId: req.userId!,
      ciphertext,
      nonce,
      algorithm,
      recipientEncryptedKeys,
      signature,
      dsaPublicKey: verifiedSenderDsaPublicKey,
  })) {
    res.status(400).json({ error: "Invalid message signature" });
    return;
  }

  const [existingMessage] = await db
    .select()
    .from(messagesTable)
    .where(and(eq(messagesTable.roomId, roomId), eq(messagesTable.senderId, req.userId!), eq(messagesTable.signature, signature!)))
    .limit(1);
  if (existingMessage) {
    res.status(200).json(messageResponse(existingMessage));
    return;
  }

  const effectiveTtl = ttlSeconds ?? room?.ttlSeconds ?? null;
  const attestExpiryOnSend = room.decayMode === EXPERIMENTAL_QUORUM_DECAY && room.ttlMode === "after_send";
  const decayAttestation: TimeQuorumAttestation | null = attestExpiryOnSend
    ? await createTimeQuorumAttestation()
    : null;
  const now = decayAttestation?.synthesizedEpochMs ?? Date.now();
  const fuzzSeconds = Math.max(0, room.deliveryFuzzSeconds);
  if (room.ttlMode === "after_send" && effectiveTtl && fuzzSeconds >= effectiveTtl) {
    res.status(400).json({ error: "Delivery fuzz must be shorter than after-send TTL" });
    return;
  }
  const fuzzDelaySeconds = fuzzSeconds > 0 ? randomInt(0, fuzzSeconds + 1) : 0;
  const availableAt = new Date(now + fuzzDelaySeconds * 1000);
  const expiresAt = effectiveTtl && room?.ttlMode === "after_send" ? new Date(now + effectiveTtl * 1000) : null;

  const [message] = await db
    .insert(messagesTable)
    .values({
      roomId,
      senderId: req.userId!,
      ciphertext,
      nonce,
      algorithm,
      signature: signature ?? null,
      senderDsaPublicKey: senderDsaPublicKey ?? sender?.dsaPublicKey ?? null,
      recipientEncryptedKeys,
      decayAttestation,
      expiresAt,
      availableAt,
      createdAt: availableAt,
    })
    .returning();

  await db
    .update(roomsTable)
    .set({ lastMessageAt: availableAt })
    .where(eq(roomsTable.id, roomId));

  const recipients = await db
    .select({ userId: roomMembersTable.userId })
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), ne(roomMembersTable.userId, req.userId!)));

  const notificationPayload = {
    title: "QuantumShield",
    body: "There is a new message to check in one of your chats.",
    url: "/app",
    tag: `room-${roomId}`,
  };

  await Promise.all(
    recipients.map((recipient) => enqueuePushNotification(recipient.userId, notificationPayload, availableAt)),
  );

  res.status(201).json(messageResponse(message));
});

router.post("/rooms/:roomId/privacy-alert", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const membership = await db
    .select()
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, req.userId!)))
    .limit(1);

  if (membership.length === 0) {
    res.status(403).json({ error: "Not a member of this room" });
    return;
  }

  const recipients = await db
    .select({ userId: roomMembersTable.userId })
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), ne(roomMembersTable.userId, req.userId!)));

  const notificationPayload = {
    title: "QuantumShield",
    body: "A privacy shield was triggered in one of your chats.",
    url: "/app",
    tag: `privacy-${roomId}`,
  };

  void Promise.all(recipients.map((recipient) => notifyUser(recipient.userId, notificationPayload)));

  res.status(202).json({ ok: true });
});

router.post("/rooms/:roomId/privacy-debug", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const membership = await db
    .select()
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, req.userId!)))
    .limit(1);

  if (membership.length === 0) {
    res.status(403).json({ error: "Not a member of this room" });
    return;
  }

  res.status(202).json({ ok: true });
});

router.delete("/rooms/:roomId/messages/:messageId", requireAuth, async (req: AuthRequest, res) => {
  const messageId = routeParam(req.params.messageId);

  await db
    .delete(messagesTable)
    .where(and(eq(messagesTable.id, messageId), eq(messagesTable.senderId, req.userId!)));

  res.json({ ok: true });
});

export default router;
