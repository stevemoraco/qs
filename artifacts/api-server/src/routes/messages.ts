import { Router } from "express";
import { db, messagesTable, roomMembersTable, roomsTable } from "@workspace/db";
import { eq, and, lt, desc, ne, inArray, isNull, lte } from "drizzle-orm";
import { randomInt } from "crypto";
import { PostRoomsRoomIdMessagesBody } from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";
import { notifyUser } from "./push";
import { logger } from "../lib/logger";
import { appendFile } from "fs/promises";

const router = Router();

function routeParam(value: string | string[] | undefined): string {
  return Array.isArray(value) ? value[0] : (value ?? "");
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
    .select({ ttlSeconds: roomsTable.ttlSeconds, ttlMode: roomsTable.ttlMode })
    .from(roomsTable)
    .where(eq(roomsTable.id, roomId))
    .limit(1);

  let query = db
    .select({
      message: messagesTable,
    })
    .from(messagesTable)
    .where(and(eq(messagesTable.roomId, roomId), lte(messagesTable.availableAt, new Date())))
    .orderBy(desc(messagesTable.createdAt))
    .limit(limit);

  if (before) {
    const [beforeMsg] = await db
      .select({ createdAt: messagesTable.createdAt })
      .from(messagesTable)
      .where(eq(messagesTable.id, before))
      .limit(1);
    if (beforeMsg) {
      query = db
        .select({
          message: messagesTable,
        })
        .from(messagesTable)
        .where(and(eq(messagesTable.roomId, roomId), lte(messagesTable.availableAt, new Date()), lt(messagesTable.createdAt, beforeMsg.createdAt)))
        .orderBy(desc(messagesTable.createdAt))
        .limit(limit);
    }
  }

  const rows = await query;

  const now = new Date();
  const visibleRows = rows.filter((r) => !r.message.expiresAt || r.message.expiresAt > now);
  const viewedExpiresAt = room?.ttlSeconds && room.ttlMode === "after_view" ? new Date(now.getTime() + room.ttlSeconds * 1000) : null;
  const firstViewedIds = viewedExpiresAt
    ? visibleRows.filter((r) => !r.message.expiresAt && r.message.senderId !== req.userId).map((r) => r.message.id)
    : [];

  if (firstViewedIds.length > 0) {
    await db
      .update(messagesTable)
      .set({ expiresAt: viewedExpiresAt })
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
      recipientEncryptedKeys: r.message.recipientEncryptedKeys,
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

  const [room] = await db
    .select({ ttlSeconds: roomsTable.ttlSeconds, ttlMode: roomsTable.ttlMode, deliveryFuzzSeconds: roomsTable.deliveryFuzzSeconds })
    .from(roomsTable)
    .where(eq(roomsTable.id, roomId))
    .limit(1);

  const effectiveTtl = ttlSeconds ?? room?.ttlSeconds ?? null;
  const now = Date.now();
  const fuzzSeconds = Math.max(0, room?.deliveryFuzzSeconds ?? 0);
  const fuzzDelaySeconds = fuzzSeconds > 0 ? randomInt(0, fuzzSeconds + 1) : 0;
  const availableAt = new Date(now + fuzzDelaySeconds * 1000);
  const expiresAt = effectiveTtl && room?.ttlMode === "after_send" ? new Date(availableAt.getTime() + effectiveTtl * 1000) : null;

  const [message] = await db
    .insert(messagesTable)
    .values({
      roomId,
      senderId: req.userId!,
      ciphertext,
      nonce,
      algorithm: algorithm ?? "AES-256-GCM+ML-KEM-1024+ML-DSA-87",
      signature: signature ?? null,
      recipientEncryptedKeys: recipientEncryptedKeys ?? null,
      expiresAt,
      availableAt,
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

  if (fuzzDelaySeconds === 0) {
    void Promise.all(recipients.map((recipient) => notifyUser(recipient.userId, notificationPayload)));
  }

  res.status(201).json({
    id: message.id,
    roomId: message.roomId,
    senderId: message.senderId,
    senderUsername: null,
    ciphertext: message.ciphertext,
    nonce: message.nonce,
    algorithm: message.algorithm,
    signature: message.signature,
    recipientEncryptedKeys: message.recipientEncryptedKeys,
    expiresAt: message.expiresAt,
    availableAt: message.availableAt,
    createdAt: message.createdAt,
  });
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

  const metrics = typeof req.body === "object" && req.body ? req.body : {};
  logger.info({ userId: req.userId, roomId, metrics }, "Privacy camera flash debug");
  void appendFile(
    "/tmp/quantumshield-flash-debug.log",
    `${JSON.stringify({ ts: new Date().toISOString(), userId: req.userId, roomId, metrics })}\n`,
  ).catch((err) => logger.warn({ err }, "Could not write privacy flash debug log"));
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
