import { Router } from "express";
import { db, usersTable, sessionsTable, leadsTable, identityCodesTable } from "@workspace/db";
import { and, count, eq, gt } from "drizzle-orm";
import argon2 from "argon2";
import { createHash, randomBytes } from "crypto";
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

function generateAuthHandle(): string {
  return randomBytes(32).toString("base64url");
}

function hashAuthHandle(authHandle: string): string {
  return createHash("sha256").update(authHandle).digest("hex");
}

function generateInternalUsername(): string {
  return `acct_${randomBytes(12).toString("hex")}`;
}

function normalizeIdentityCode(code: string): string {
  return code.trim().toLowerCase();
}

function isValidIdentityCode(code: string): boolean {
  return /^[a-z0-9][a-z0-9_-]{1,31}$/.test(code);
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

  const { passcode, primaryCode, displayName, kemPublicKey, dsaPublicKey, leadEmail } = parse.data;
  const normalizedPrimaryCode = primaryCode ? normalizeIdentityCode(primaryCode) : null;

  if (normalizedPrimaryCode && !isValidIdentityCode(normalizedPrimaryCode)) {
    res.status(400).json({ error: "Code must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }

  if (normalizedPrimaryCode) {
    const existing = await db
      .select({ id: identityCodesTable.id })
      .from(identityCodesTable)
      .where(eq(identityCodesTable.code, normalizedPrimaryCode))
      .limit(1);

    if (existing.length > 0) {
      res.status(409).json({ error: "Code already claimed" });
      return;
    }
  }

  const authHandle = generateAuthHandle();
  const passwordHash = await argon2.hash(passcode);

  const [user] = await db
    .insert(usersTable)
    .values({
      username: generateInternalUsername(),
      authHandleHash: hashAuthHandle(authHandle),
      passwordHash,
      displayName: displayName ?? null,
      avatarColor: randomColor(),
      kemPublicKey,
      dsaPublicKey,
    })
    .returning();

  if (normalizedPrimaryCode) {
    const expiresAt = new Date();
    expiresAt.setFullYear(expiresAt.getFullYear() + 10);
    await db.insert(identityCodesTable).values({
      ownerUserId: user.id,
      code: normalizedPrimaryCode,
      kind: "alias",
      expiresAt,
    });
  }

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
    authHandle,
    user: {
      id: user.id,
      username: normalizedPrimaryCode ?? "sealed",
      primaryCode: normalizedPrimaryCode,
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

  const { authHandle, passcode } = parse.data;

  const [user] = await db
    .select()
    .from(usersTable)
    .where(eq(usersTable.authHandleHash, hashAuthHandle(authHandle)))
    .limit(1);

  if (!user) {
    res.status(401).json({ error: "Invalid passcode" });
    return;
  }

  const valid = await argon2.verify(user.passwordHash, passcode);
  if (!valid) {
    res.status(401).json({ error: "Invalid passcode" });
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
    authHandle,
    user: {
      id: user.id,
      username: "sealed",
      primaryCode: null,
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
    username: "sealed",
    primaryCode: null,
    displayName: u.displayName,
    avatarColor: u.avatarColor,
    kemPublicKey: u.kemPublicKey,
    dsaPublicKey: u.dsaPublicKey,
    createdAt: u.createdAt,
  });
});

router.get("/auth/devices", requireAuth, async (req: AuthRequest, res) => {
  const [row] = await db
    .select({ count: count() })
    .from(sessionsTable)
    .where(and(eq(sessionsTable.userId, req.userId!), gt(sessionsTable.expiresAt, new Date())));

  res.json({
    activeDeviceCount: row?.count ?? 0,
  });
});

router.post("/auth/logout", requireAuth, async (req: AuthRequest, res) => {
  const token = req.headers.authorization!.slice(7);
  await db.delete(sessionsTable).where(eq(sessionsTable.token, token));
  res.json({ ok: true });
});

export default router;
