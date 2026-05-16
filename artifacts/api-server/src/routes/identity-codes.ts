import { Router } from "express";
import { db, identityCodesTable, usersTable } from "@workspace/db";
import { and, eq, gt, ilike, isNull, or } from "drizzle-orm";
import {
  PatchIdentityCodesCodeIdBody,
  PostIdentityCodesBody,
} from "@workspace/api-zod";
import { randomBytes } from "crypto";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

function routeParam(value: string | string[] | undefined): string {
  return Array.isArray(value) ? value[0] : (value ?? "");
}

function normalizeIdentityCode(code: string): string {
  return code.trim().replace(/^[@#]+/, "").toLowerCase();
}

function isValidIdentityCode(code: string): boolean {
  return /^[a-z0-9][a-z0-9_-]{1,31}$/.test(code);
}

function expiryFromTtl(ttlSeconds: number | null | undefined): Date | null {
  if (!ttlSeconds) return null;
  return new Date(Date.now() + ttlSeconds * 1000);
}

function randomCode(): string {
  return randomBytes(6).toString("base64url").toLowerCase().replace(/[^a-z0-9]/g, "").slice(0, 8);
}

function publicIdentityCode(code: typeof identityCodesTable.$inferSelect) {
  return {
    id: code.id,
    code: code.code,
    kind: code.kind,
    visibilityScope: code.visibilityScope,
    active: code.active,
    maxUses: code.maxUses,
    useCount: code.useCount,
    allowedCodes: code.allowedCodes ?? null,
    expiresAt: code.expiresAt,
    rolledAt: code.rolledAt,
    createdAt: code.createdAt,
    updatedAt: code.updatedAt,
  };
}

router.get("/identity-codes", requireAuth, async (req: AuthRequest, res) => {
  const rows = await db
    .select()
    .from(identityCodesTable)
    .where(eq(identityCodesTable.ownerUserId, req.userId!));

  res.json(rows.map(publicIdentityCode));
});

router.post("/identity-codes", requireAuth, async (req: AuthRequest, res) => {
  const parse = PostIdentityCodesBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const requestedCode = parse.data.code ? normalizeIdentityCode(parse.data.code) : randomCode();
  if (!isValidIdentityCode(requestedCode)) {
    res.status(400).json({ error: "Code must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }

  const existing = await db
    .select({ id: identityCodesTable.id })
    .from(identityCodesTable)
    .where(eq(identityCodesTable.code, requestedCode))
    .limit(1);

  if (existing.length > 0) {
    res.status(409).json({ error: "Code already claimed" });
    return;
  }

  const [code] = await db
    .insert(identityCodesTable)
    .values({
      ownerUserId: req.userId!,
      code: requestedCode,
      kind: parse.data.kind ?? "alias",
      visibilityScope: parse.data.visibilityScope ?? "public",
      active: true,
      maxUses: parse.data.maxUses ?? null,
      allowedCodes: parse.data.allowedCodes ?? null,
      expiresAt: expiryFromTtl(parse.data.ttlSeconds),
      updatedAt: new Date(),
    })
    .returning();

  res.status(201).json(publicIdentityCode(code));
});

router.patch("/identity-codes/:codeId", requireAuth, async (req: AuthRequest, res) => {
  const codeId = routeParam(req.params.codeId);
  const parse = PatchIdentityCodesCodeIdBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const [existing] = await db
    .select()
    .from(identityCodesTable)
    .where(and(eq(identityCodesTable.id, codeId), eq(identityCodesTable.ownerUserId, req.userId!)))
    .limit(1);

  if (!existing) {
    res.status(404).json({ error: "Code not found" });
    return;
  }

  const nextActive = parse.data.active ?? existing.active;
  const [updated] = await db
    .update(identityCodesTable)
    .set({
      active: nextActive,
      visibilityScope: parse.data.visibilityScope ?? existing.visibilityScope,
      maxUses: parse.data.maxUses === undefined ? existing.maxUses : parse.data.maxUses,
      allowedCodes: parse.data.allowedCodes === undefined ? existing.allowedCodes : parse.data.allowedCodes,
      expiresAt: parse.data.ttlSeconds === undefined ? existing.expiresAt : expiryFromTtl(parse.data.ttlSeconds),
      rolledAt: nextActive ? existing.rolledAt : new Date(),
      updatedAt: new Date(),
    })
    .where(and(eq(identityCodesTable.id, codeId), eq(identityCodesTable.ownerUserId, req.userId!)))
    .returning();

  res.json(publicIdentityCode(updated));
});

router.get("/identity-codes/search", requireAuth, async (req: AuthRequest, res) => {
  const q = normalizeIdentityCode(String(req.query.q ?? ""));
  if (!q) {
    res.json([]);
    return;
  }

  const rows = await db
    .select({ code: identityCodesTable, user: usersTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .where(
      and(
        ilike(identityCodesTable.code, `%${q}%`),
        eq(identityCodesTable.active, true),
        eq(identityCodesTable.visibilityScope, "public"),
        or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
      )
    )
    .limit(20);

  res.json(
    rows.map(({ code, user }) => ({
      id: user.id,
      username: code.code,
      primaryCode: code.code,
      displayName: user.displayName,
      avatarColor: user.avatarColor,
      kemPublicKey: user.kemPublicKey,
      dsaPublicKey: user.dsaPublicKey,
      createdAt: user.createdAt,
    }))
  );
});

export default router;
