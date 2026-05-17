import { Router } from "express";
import { db, identityCodesTable, usersTable } from "@workspace/db";
import { and, eq, gt, isNull, or } from "drizzle-orm";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

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

function normalizeIdentityCode(code: string): string {
  return code.trim().replace(/^[@#]+/, "").toLowerCase();
}

function isValidLookupHash(code: string): boolean {
  return /^[a-f0-9]{64}$/.test(code);
}

router.get("/users/search", requireAuth, async (req: AuthRequest, res) => {
  const q = normalizeIdentityCode(String(req.query.q ?? ""));
  if (!q || !isValidLookupHash(q)) {
    res.json([]);
    return;
  }

  const users = await db
    .select({ user: usersTable, code: identityCodesTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .where(
      and(
        eq(identityCodesTable.code, q),
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
