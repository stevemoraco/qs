import { Router } from "express";
import { db, identityCodesTable, roomMembersTable, usersTable } from "@workspace/db";
import { and, eq, gt, inArray, isNull, or } from "drizzle-orm";
import { requireAuth, type AuthRequest } from "../middlewares/auth";
import {
  canAcceptIdentityLookupInput,
  isValidIdentityCode,
  normalizeIdentityCode,
  serverLookupCode,
} from "../lib/identity-lookup";
import { consumeRateLimit } from "../lib/rate-limit";

const router = Router();

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

function searchUser(u: typeof usersTable.$inferSelect, searchedCode: string | null) {
  return {
    id: u.id,
    username: searchedCode ?? "sealed",
    primaryCode: searchedCode,
    displayName: u.displayName,
    avatarColor: u.avatarColor,
    kemPublicKey: u.kemPublicKey,
    dsaPublicKey: u.dsaPublicKey,
    createdAt: u.createdAt,
  };
}

async function canReadUserProfile(requesterId: string, targetUserId: string): Promise<boolean> {
  if (requesterId === targetUserId) return true;

  const requesterRooms = await db
    .select({ roomId: roomMembersTable.roomId })
    .from(roomMembersTable)
    .where(eq(roomMembersTable.userId, requesterId));
  if (requesterRooms.length === 0) return false;

  const [sharedRoom] = await db
    .select({ roomId: roomMembersTable.roomId })
    .from(roomMembersTable)
    .where(and(eq(roomMembersTable.userId, targetUserId), inArray(roomMembersTable.roomId, requesterRooms.map((room) => room.roomId))))
    .limit(1);
  return !!sharedRoom;
}

router.get("/users/search", requireAuth, async (req: AuthRequest, res) => {
  const q = normalizeIdentityCode(String(req.query.q ?? ""));
  if (!q || !canAcceptIdentityLookupInput(q)) {
    res.json([]);
    return;
  }
  const lookup = serverLookupCode(q);
  const displayCode = isValidIdentityCode(q) ? q : null;

  if (!consumeRateLimit(`users:search:${req.ip ?? "unknown"}:${req.userId}:${lookup}`, 120, 5 * 60 * 1000, 2 * 60 * 1000)) {
    res.status(429).json({ error: "Too many handle attempts. Try again later." });
    return;
  }

  const users = await db
    .select({ user: usersTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .where(
      and(
        eq(identityCodesTable.code, lookup),
        eq(identityCodesTable.active, true),
        eq(identityCodesTable.visibilityScope, "public"),
        or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
      )
    )
    .limit(1);

  res.json(users.map(({ user }) => searchUser(user, displayCode)));
});

router.get("/users/:userId", requireAuth, async (req: AuthRequest, res) => {
  const userId = routeParam(req.params.userId);

  if (!(await canReadUserProfile(req.userId!, userId))) {
    res.status(404).json({ error: "User not found" });
    return;
  }

  const [user] = await db
    .select()
    .from(usersTable)
    .where(eq(usersTable.id, userId))
    .limit(1);

  if (!user) {
    res.status(404).json({ error: "User not found" });
    return;
  }

  res.json(publicUser(user));
});

export default router;
