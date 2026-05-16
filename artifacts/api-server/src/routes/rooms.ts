import { Router } from "express";
import { db, roomsTable, roomMembersTable, usersTable, messagesTable } from "@workspace/db";
import { eq, and, count, sql } from "drizzle-orm";
import { PostRoomsBody, PostRoomsRoomIdMembersBody } from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

function routeParam(value: string | string[] | undefined): string {
  return Array.isArray(value) ? value[0] : (value ?? "");
}

function publicUser(u: typeof usersTable.$inferSelect) {
  return {
    id: u.id,
    username: u.username,
    displayName: u.displayName,
    avatarColor: u.avatarColor,
    kemPublicKey: u.kemPublicKey,
    dsaPublicKey: u.dsaPublicKey,
    createdAt: u.createdAt,
  };
}

router.get("/rooms", requireAuth, async (req: AuthRequest, res) => {
  const memberships = await db
    .select({ roomId: roomMembersTable.roomId })
    .from(roomMembersTable)
    .where(eq(roomMembersTable.userId, req.userId!));

  if (memberships.length === 0) {
    res.json([]);
    return;
  }

  const roomIds = memberships.map((m) => m.roomId);
  const rooms = [];

  for (const roomId of roomIds) {
    const [room] = await db
      .select()
      .from(roomsTable)
      .where(eq(roomsTable.id, roomId))
      .limit(1);

    if (!room) continue;

    const [{ memberCount }] = await db
      .select({ memberCount: count() })
      .from(roomMembersTable)
      .where(eq(roomMembersTable.roomId, roomId));

    const members = await db
      .select({ user: usersTable })
      .from(roomMembersTable)
      .innerJoin(usersTable, eq(roomMembersTable.userId, usersTable.id))
      .where(eq(roomMembersTable.roomId, roomId));

    rooms.push({
      id: room.id,
      name: room.name,
      type: room.type,
      memberCount: Number(memberCount),
      ttlSeconds: room.ttlSeconds,
      lastMessageAt: room.lastMessageAt,
      createdAt: room.createdAt,
      members: members.map((m) => publicUser(m.user)),
    });
  }

  res.json(rooms);
});

router.post("/rooms", requireAuth, async (req: AuthRequest, res) => {
  const parse = PostRoomsBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { name, type, memberIds, ttlSeconds } = parse.data;
  const allMemberIds = Array.from(new Set([req.userId!, ...(memberIds ?? [])]));

  const [room] = await db
    .insert(roomsTable)
    .values({ name: name ?? null, type, ttlSeconds: ttlSeconds ?? null })
    .returning();

  for (const userId of allMemberIds) {
    await db.insert(roomMembersTable).values({ roomId: room.id, userId }).onConflictDoNothing();
  }

  const [{ memberCount }] = await db
    .select({ memberCount: count() })
    .from(roomMembersTable)
    .where(eq(roomMembersTable.roomId, room.id));

  res.status(201).json({
    id: room.id,
    name: room.name,
    type: room.type,
    memberCount: Number(memberCount),
    ttlSeconds: room.ttlSeconds,
    lastMessageAt: room.lastMessageAt,
    createdAt: room.createdAt,
    members: null,
  });
});

router.get("/rooms/:roomId", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const membership = await db
    .select()
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, req.userId!)))
    .limit(1);

  if (membership.length === 0) {
    res.status(404).json({ error: "Room not found" });
    return;
  }

  const [room] = await db
    .select()
    .from(roomsTable)
    .where(eq(roomsTable.id, roomId))
    .limit(1);

  if (!room) {
    res.status(404).json({ error: "Room not found" });
    return;
  }

  const [{ memberCount }] = await db
    .select({ memberCount: count() })
    .from(roomMembersTable)
    .where(eq(roomMembersTable.roomId, roomId));

  const members = await db
    .select({ user: usersTable })
    .from(roomMembersTable)
    .innerJoin(usersTable, eq(roomMembersTable.userId, usersTable.id))
    .where(eq(roomMembersTable.roomId, roomId));

  res.json({
    id: room.id,
    name: room.name,
    type: room.type,
    memberCount: Number(memberCount),
    ttlSeconds: room.ttlSeconds,
    lastMessageAt: room.lastMessageAt,
    createdAt: room.createdAt,
    members: members.map((m) => publicUser(m.user)),
  });
});

router.delete("/rooms/:roomId", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const membership = await db
    .select()
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, req.userId!)))
    .limit(1);

  if (membership.length === 0) {
    res.status(404).json({ error: "Room not found" });
    return;
  }

  await db.delete(roomsTable).where(eq(roomsTable.id, roomId));
  res.json({ ok: true });
});

router.get("/rooms/:roomId/members", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);

  const members = await db
    .select({ user: usersTable })
    .from(roomMembersTable)
    .innerJoin(usersTable, eq(roomMembersTable.userId, usersTable.id))
    .where(eq(roomMembersTable.roomId, roomId));

  res.json(members.map((m) => publicUser(m.user)));
});

router.post("/rooms/:roomId/members", requireAuth, async (req: AuthRequest, res) => {
  const roomId = routeParam(req.params.roomId);
  const parse = PostRoomsRoomIdMembersBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { userId } = parse.data;
  await db
    .insert(roomMembersTable)
    .values({ roomId, userId })
    .onConflictDoNothing();

  res.json({ ok: true });
});

export default router;
