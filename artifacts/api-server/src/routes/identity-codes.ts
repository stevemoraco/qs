import { Router } from "express";
import { db, identityCodesTable, usersTable } from "@workspace/db";
import { and, asc, count, desc, eq, gt, isNull, or } from "drizzle-orm";
import {
  PatchIdentityCodesCodeIdBody,
  PostIdentityCodesBody,
} from "@workspace/api-zod";
import { randomBytes } from "crypto";
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

function publicSearchUser(user: typeof usersTable.$inferSelect, searchedCode: string | null) {
  return {
    id: user.id,
    username: searchedCode ?? "sealed",
    primaryCode: searchedCode,
    displayName: user.displayName,
    avatarColor: user.avatarColor,
    kemPublicKey: user.kemPublicKey,
    dsaPublicKey: user.dsaPublicKey,
    createdAt: user.createdAt,
  };
}

router.get("/identity-codes", requireAuth, async (req: AuthRequest, res) => {
  const rows = await db
    .select()
    .from(identityCodesTable)
    .where(eq(identityCodesTable.ownerUserId, req.userId!))
    .orderBy(
      asc(identityCodesTable.kind),
      desc(identityCodesTable.active),
      asc(identityCodesTable.code),
      asc(identityCodesTable.createdAt)
    );

  res.json(rows.map(publicIdentityCode));
});

router.post("/identity-codes", requireAuth, async (req: AuthRequest, res) => {
  const parse = PostIdentityCodesBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const kind = parse.data.kind ?? "alias";
  const requestedInput = parse.data.code ? normalizeIdentityCode(parse.data.code) : randomCode();
  if (kind === "alias" ? !canAcceptIdentityLookupInput(requestedInput) : !isValidIdentityCode(requestedInput)) {
    res.status(400).json({ error: kind === "alias" ? "Handle lookup hash is invalid" : "Code must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }
  const requestedCode = kind === "alias" ? serverLookupCode(requestedInput) : requestedInput;

  if (kind === "alias" && !consumeRateLimit(`identity-code:create:${req.ip ?? "unknown"}:${requestedCode}`, 25, 10 * 60 * 1000, 5 * 60 * 1000)) {
    res.status(429).json({ error: "Too many handle attempts. Try again later." });
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
      kind,
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

router.post("/identity-codes/unseal", requireAuth, async (req: AuthRequest, res) => {
  const input = typeof req.body?.code === "string" ? normalizeIdentityCode(req.body.code) : "";
  if (!canAcceptIdentityLookupInput(input)) {
    res.status(400).json({ error: "Enter a valid handle to unseal." });
    return;
  }

  const lookup = serverLookupCode(input);
  const [code] = await db
    .select()
    .from(identityCodesTable)
    .where(and(
      eq(identityCodesTable.ownerUserId, req.userId!),
      eq(identityCodesTable.kind, "alias"),
      eq(identityCodesTable.code, lookup)
    ))
    .limit(1);

  if (!code) {
    res.status(404).json({ error: "That handle is not one of your sealed handles." });
    return;
  }

  res.json(publicIdentityCode(code));
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
  if (existing.kind === "alias" && existing.active && nextActive === false) {
    const [activeAliasCount] = await db
      .select({ count: count() })
      .from(identityCodesTable)
      .where(
        and(
          eq(identityCodesTable.ownerUserId, req.userId!),
          eq(identityCodesTable.kind, "alias"),
          eq(identityCodesTable.active, true),
          or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
        )
      );
    const isLastActiveHandle = (activeAliasCount?.count ?? 0) <= 1;
    const freshSession = !!req.sessionCreatedAt && Date.now() - req.sessionCreatedAt.getTime() < 5 * 60 * 1000;
    if (isLastActiveHandle && (!parse.data.confirmLastHandleDisable || !freshSession)) {
      res.status(409).json({
        error: "Disabling the last active handle requires triple confirmation and fresh passkey or device verification.",
      });
      return;
    }
  }

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
  if (!q || !canAcceptIdentityLookupInput(q)) {
    res.json([]);
    return;
  }
  const lookup = serverLookupCode(q);
  const displayCode = isValidIdentityCode(q) ? q : null;

  if (!consumeRateLimit(`identity-code:search:${req.ip ?? "unknown"}:${lookup}`, 120, 5 * 60 * 1000, 2 * 60 * 1000)) {
    res.status(429).json({ error: "Too many handle attempts. Try again later." });
    return;
  }

  const rows = await db
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

  res.json(rows.map(({ user }) => publicSearchUser(user, displayCode)));
});

export default router;
