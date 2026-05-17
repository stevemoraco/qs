import { Router } from "express";
import { db, roomsTable, roomMembersTable, usersTable } from "@workspace/db";
import { eq, and, count } from "drizzle-orm";
import { PostRoomsBody, PostRoomsRoomIdMembersBody } from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();
const DEFAULT_ROOM_TTL_SECONDS = 300;
const DEFAULT_ROOM_TTL_MODE = "after_view";
const DEFAULT_DELIVERY_FUZZ_SECONDS = 89;
const DEFAULT_DECAY_MODE = "standard";
const MAX_ROOM_TTL_SECONDS = 35_337_600;
const MAX_DELIVERY_FUZZ_SECONDS = 35_337_600;

function routeParam(value: string | string[] | undefined): string {
  return Array.isArray(value) ? value[0] : (value ?? "");
}

function publicUser(u: typeof usersTable.$inferSelect) {
  return {
    id: u.id,
    username: "sealed",
    primaryCode: null,
    displayName: u.displayName,
    avatarColor: u.avatarColor,
    kemPublicKey: u.kemPublicKey,
    dsaPublicKey: u.dsaPublicKey,
    createdAt: u.createdAt,
  };
}

function validDurationSeconds(value: number | null | undefined, max: number): boolean {
  if (value === null || value === undefined) return true;
  return Number.isSafeInteger(value) && value >= 0 && value <= max;
}

async function isRoomMember(roomId: string, userId: string): Promise<boolean> {
  const membership = await db
    .select({ userId: roomMembersTable.userId })
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.roomId, roomId), eq(roomMembersTable.userId, userId)))
    .limit(1);
  return membership.length > 0;
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
      ttlMode: room.ttlMode,
      deliveryFuzzSeconds: room.deliveryFuzzSeconds,
      decayMode: room.decayMode,
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

  const { name, type, memberIds, ttlSeconds, ttlMode, deliveryFuzzSeconds, decayMode } = parse.data;
  if (!validDurationSeconds(ttlSeconds, MAX_ROOM_TTL_SECONDS) || !validDurationSeconds(deliveryFuzzSeconds, MAX_DELIVERY_FUZZ_SECONDS)) {
    res.status(400).json({ error: "Invalid TTL or delivery fuzz window" });
    return;
  }
  const effectiveTtl = ttlSeconds === undefined ? DEFAULT_ROOM_TTL_SECONDS : ttlSeconds;
  const effectiveTtlMode = ttlMode ?? DEFAULT_ROOM_TTL_MODE;
  const effectiveDeliveryFuzz = deliveryFuzzSeconds ?? DEFAULT_DELIVERY_FUZZ_SECONDS;
  const effectiveDecayMode = decayMode ?? DEFAULT_DECAY_MODE;
  if (effectiveTtlMode === "after_send" && effectiveTtl && effectiveDeliveryFuzz >= effectiveTtl) {
    res.status(400).json({ error: "Delivery fuzz must be shorter than after-send TTL" });
    return;
  }

  const allMemberIds = Array.from(new Set([req.userId!, ...(memberIds ?? [])]));

  const [room] = await db
    .insert(roomsTable)
    .values({
      name: name ?? null,
      type,
      ttlSeconds: effectiveTtl,
      ttlMode: effectiveTtlMode,
      deliveryFuzzSeconds: effectiveDeliveryFuzz,
      decayMode: effectiveDecayMode,
    })
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
    ttlMode: room.ttlMode,
    deliveryFuzzSeconds: room.deliveryFuzzSeconds,
    decayMode: room.decayMode,
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
    ttlMode: room.ttlMode,
    deliveryFuzzSeconds: room.deliveryFuzzSeconds,
    decayMode: room.decayMode,
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

  if (!(await isRoomMember(roomId, req.userId!))) {
    res.status(404).json({ error: "Room not found" });
    return;
  }

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
  if (!(await isRoomMember(roomId, req.userId!))) {
    res.status(404).json({ error: "Room not found" });
    return;
  }

  const [user] = await db
    .select({ id: usersTable.id })
    .from(usersTable)
    .where(eq(usersTable.id, userId))
    .limit(1);
  if (!user) {
    res.status(404).json({ error: "User not found" });
    return;
  }

  await db
    .insert(roomMembersTable)
    .values({ roomId, userId })
    .onConflictDoNothing();

  res.json({ ok: true });
});

export default router;
