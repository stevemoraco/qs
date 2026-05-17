import { Router } from "express";
import { db, identityCodesTable, usersTable } from "@workspace/db";
import { and, eq, gt, isNull, or } from "drizzle-orm";
import { requireAuth, type AuthRequest } from "../middlewares/auth";
import {
  canAcceptIdentityLookupInput,
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

router.get("/users/search", requireAuth, async (req: AuthRequest, res) => {
  const q = normalizeIdentityCode(String(req.query.q ?? ""));
  if (!q || !canAcceptIdentityLookupInput(q)) {
    res.json([]);
    return;
  }
  const lookup = serverLookupCode(q);

  if (!consumeRateLimit(`users:search:${req.ip ?? "unknown"}:${req.userId}:${lookup}`, 10, 5 * 60 * 1000, 30 * 60 * 1000)) {
    res.status(429).json({ error: "Too many handle attempts. Try again later." });
    return;
  }

  const users = await db
    .select({ user: usersTable, code: identityCodesTable })
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
    .limit(20);

  res.json(users.map(({ user, code }) => ({ ...publicUser(user), username: code.code, primaryCode: code.code })));
});

router.get("/users/:userId", requireAuth, async (req: AuthRequest, res) => {
  const userId = routeParam(req.params.userId);

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
