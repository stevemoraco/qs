import { Router } from "express";
import { db, usersTable, sessionsTable, leadsTable } from "@workspace/db";
import { eq } from "drizzle-orm";
import argon2 from "argon2";
import { randomBytes } from "crypto";
import {
  PostAuthRegisterBody,
  PostAuthLoginBody,
} from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

const AVATAR_COLORS = [
  "#06b6d4","#8b5cf6","#10b981","#f59e0b","#ef4444",
  "#ec4899","#6366f1","#14b8a6","#f97316","#84cc16",
];

function randomColor() {
  return AVATAR_COLORS[Math.floor(Math.random() * AVATAR_COLORS.length)];
}

function generateToken(): string {
  return randomBytes(48).toString("hex");
}

function sessionExpiresAt(): Date {
  const d = new Date();
  d.setDate(d.getDate() + 30);
  return d;
}

router.post("/auth/register", async (req, res) => {
  const parse = PostAuthRegisterBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { username, password, displayName, kemPublicKey, dsaPublicKey, leadEmail } = parse.data;

  const existing = await db
    .select({ id: usersTable.id })
    .from(usersTable)
    .where(eq(usersTable.username, username.toLowerCase()))
    .limit(1);

  if (existing.length > 0) {
    res.status(409).json({ error: "Username already taken" });
    return;
  }

  const passwordHash = await argon2.hash(password);

  const [user] = await db
    .insert(usersTable)
    .values({
      username: username.toLowerCase(),
      passwordHash,
      displayName: displayName ?? null,
      avatarColor: randomColor(),
      kemPublicKey,
      dsaPublicKey,
    })
    .returning();

  const token = generateToken();
  await db.insert(sessionsTable).values({
    userId: user.id,
    token,
    expiresAt: sessionExpiresAt(),
  });

  if (leadEmail) {
    await db
      .insert(leadsTable)
      .values({
        email: leadEmail.trim().toLowerCase(),
        name: displayName ?? null,
        currentStep: 3,
        accountUserId: user.id,
        source: "homepage",
        updatedAt: new Date(),
      })
      .onConflictDoUpdate({
        target: leadsTable.email,
        set: {
          currentStep: 3,
          accountUserId: user.id,
          name: displayName ?? null,
          updatedAt: new Date(),
        },
      });
  }

  res.status(201).json({
    token,
    user: {
      id: user.id,
      username: user.username,
      displayName: user.displayName,
      avatarColor: user.avatarColor,
      kemPublicKey: user.kemPublicKey,
      dsaPublicKey: user.dsaPublicKey,
      createdAt: user.createdAt,
    },
  });
});

router.post("/auth/login", async (req, res) => {
  const parse = PostAuthLoginBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { username, password } = parse.data;

  const [user] = await db
    .select()
    .from(usersTable)
    .where(eq(usersTable.username, username.toLowerCase()))
    .limit(1);

  if (!user) {
    res.status(401).json({ error: "Invalid username or password" });
    return;
  }

  const valid = await argon2.verify(user.passwordHash, password);
  if (!valid) {
    res.status(401).json({ error: "Invalid username or password" });
    return;
  }

  const token = generateToken();
  await db.insert(sessionsTable).values({
    userId: user.id,
    token,
    expiresAt: sessionExpiresAt(),
  });

  res.json({
    token,
    user: {
      id: user.id,
      username: user.username,
      displayName: user.displayName,
      avatarColor: user.avatarColor,
      kemPublicKey: user.kemPublicKey,
      dsaPublicKey: user.dsaPublicKey,
      createdAt: user.createdAt,
    },
  });
});

router.get("/auth/me", requireAuth, (req: AuthRequest, res) => {
  const u = req.user!;
  res.json({
    id: u.id,
    username: u.username,
    displayName: u.displayName,
    avatarColor: u.avatarColor,
    kemPublicKey: u.kemPublicKey,
    dsaPublicKey: u.dsaPublicKey,
    createdAt: u.createdAt,
  });
});

router.post("/auth/logout", requireAuth, async (req: AuthRequest, res) => {
  const token = req.headers.authorization!.slice(7);
  await db.delete(sessionsTable).where(eq(sessionsTable.token, token));
  res.json({ ok: true });
});

export default router;
