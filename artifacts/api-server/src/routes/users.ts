import { Router } from "express";
import { db, usersTable } from "@workspace/db";
import { eq, ilike } from "drizzle-orm";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

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

router.get("/users/search", requireAuth, async (req: AuthRequest, res) => {
  const q = String(req.query.q ?? "").trim();
  if (!q) {
    res.json([]);
    return;
  }

  const users = await db
    .select()
    .from(usersTable)
    .where(ilike(usersTable.username, `%${q}%`))
    .limit(20);

  res.json(users.map(publicUser));
});

router.get("/users/:userId", requireAuth, async (req: AuthRequest, res) => {
  const [user] = await db
    .select()
    .from(usersTable)
    .where(eq(usersTable.id, req.params.userId))
    .limit(1);

  if (!user) {
    res.status(404).json({ error: "User not found" });
    return;
  }

  res.json(publicUser(user));
});

export default router;
