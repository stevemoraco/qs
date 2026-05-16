import { Router } from "express";
import { db, messagesTable, roomMembersTable, roomsTable, usersTable } from "@workspace/db";
import { eq, and, lt, desc, sql } from "drizzle-orm";
import { PostRoomsRoomIdMessagesBody } from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

router.get("/rooms/:roomId/messages", requireAuth, async (req: AuthRequest, res) => {
  const { roomId } = req.params;

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

  let query = db
    .select({
      message: messagesTable,
      senderUsername: usersTable.username,
    })
    .from(messagesTable)
    .leftJoin(usersTable, eq(messagesTable.senderId, usersTable.id))
    .where(eq(messagesTable.roomId, roomId))
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
          senderUsername: usersTable.username,
        })
        .from(messagesTable)
        .leftJoin(usersTable, eq(messagesTable.senderId, usersTable.id))
        .where(and(eq(messagesTable.roomId, roomId), lt(messagesTable.createdAt, beforeMsg.createdAt)))
        .orderBy(desc(messagesTable.createdAt))
        .limit(limit);
    }
  }

  const rows = await query;

  const now = new Date();
  const messages = rows
    .filter((r) => !r.message.expiresAt || r.message.expiresAt > now)
    .map((r) => ({
      id: r.message.id,
      roomId: r.message.roomId,
      senderId: r.message.senderId,
      senderUsername: r.senderUsername,
      ciphertext: r.message.ciphertext,
      nonce: r.message.nonce,
      algorithm: r.message.algorithm,
      signature: r.message.signature,
      recipientEncryptedKeys: r.message.recipientEncryptedKeys,
      expiresAt: r.message.expiresAt,
      createdAt: r.message.createdAt,
    }));

  res.json(messages.reverse());
});

router.post("/rooms/:roomId/messages", requireAuth, async (req: AuthRequest, res) => {
  const { roomId } = req.params;

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
    .select({ ttlSeconds: roomsTable.ttlSeconds })
    .from(roomsTable)
    .where(eq(roomsTable.id, roomId))
    .limit(1);

  const effectiveTtl = ttlSeconds ?? room?.ttlSeconds ?? null;
  let expiresAt: Date | null = null;
  if (effectiveTtl) {
    expiresAt = new Date(Date.now() + effectiveTtl * 1000);
  }

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
    })
    .returning();

  await db
    .update(roomsTable)
    .set({ lastMessageAt: new Date() })
    .where(eq(roomsTable.id, roomId));

  const [sender] = await db
    .select({ username: usersTable.username })
    .from(usersTable)
    .where(eq(usersTable.id, req.userId!))
    .limit(1);

  res.status(201).json({
    id: message.id,
    roomId: message.roomId,
    senderId: message.senderId,
    senderUsername: sender?.username ?? null,
    ciphertext: message.ciphertext,
    nonce: message.nonce,
    algorithm: message.algorithm,
    signature: message.signature,
    recipientEncryptedKeys: message.recipientEncryptedKeys,
    expiresAt: message.expiresAt,
    createdAt: message.createdAt,
  });
});

router.delete("/rooms/:roomId/messages/:messageId", requireAuth, async (req: AuthRequest, res) => {
  const { messageId } = req.params;

  await db
    .delete(messagesTable)
    .where(and(eq(messagesTable.id, messageId), eq(messagesTable.senderId, req.userId!)));

  res.json({ ok: true });
});

export default router;
