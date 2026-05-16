import { Router } from "express";
import { db, usersTable, sessionsTable, leadsTable, identityCodesTable, deviceCredentialsTable } from "@workspace/db";
import { and, count, eq, gt, isNull, or } from "drizzle-orm";
import argon2 from "argon2";
import { createHash, randomBytes } from "crypto";
import {
  generateAuthenticationOptions,
  generateRegistrationOptions,
  verifyAuthenticationResponse,
  verifyRegistrationResponse,
} from "@simplewebauthn/server";
import type {
  AuthenticationResponseJSON,
  AuthenticatorTransportFuture,
  RegistrationResponseJSON,
} from "@simplewebauthn/server";
import {
  PostAuthRegisterBody,
  PostAuthLoginBody,
} from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";
import { notifyUser } from "./push";

const router = Router();

const AVATAR_COLORS = [
  "#06b6d4","#8b5cf6","#10b981","#f59e0b","#ef4444",
  "#ec4899","#6366f1","#14b8a6","#f97316","#84cc16",
];

const loginFailures = new Map<string, { count: number; lockedUntil: number }>();
const passkeyChallenges = new Map<string, { handle: string; expiresAt: number }>();

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

function publicOrigin(req: { get(name: string): string | undefined; protocol: string }): string {
  const host = req.get("x-forwarded-host") ?? req.get("host") ?? "localhost";
  const proto = req.get("x-forwarded-proto") ?? req.protocol ?? "https";
  return `${proto}://${host}`;
}

function rpId(req: { get(name: string): string | undefined }): string {
  return (req.get("x-forwarded-host") ?? req.get("host") ?? "localhost").split(":")[0];
}

function rememberChallenge(challenge: string, handle: string): void {
  passkeyChallenges.set(challenge, { handle, expiresAt: Date.now() + 5 * 60 * 1000 });
}

function consumeChallenge(challenge: string, handle: string): boolean {
  const saved = passkeyChallenges.get(challenge);
  passkeyChallenges.delete(challenge);
  return !!saved && saved.handle === handle && saved.expiresAt > Date.now();
}

function normalizeIdentityCode(code: string): string {
  return code.trim().replace(/^[@#]+/, "").toLowerCase();
}

function isValidIdentityCode(code: string): boolean {
  return /^[a-z0-9][a-z0-9_-]{1,31}$/.test(code);
}

function isRegistrationResponse(value: unknown): value is RegistrationResponseJSON {
  return !!value && typeof value === "object" && "id" in value && "response" in value;
}

function isAuthenticationResponse(value: unknown): value is AuthenticationResponseJSON {
  return !!value && typeof value === "object" && "id" in value && "response" in value;
}

function expiryFromTtl(ttlSeconds: number | null | undefined): Date | null {
  if (!ttlSeconds) return null;
  return new Date(Date.now() + ttlSeconds * 1000);
}

function sessionExpiresAt(): Date {
  const d = new Date();
  d.setDate(d.getDate() + 30);
  return d;
}

async function createSession(userId: string): Promise<string> {
  const token = generateToken();
  await db.insert(sessionsTable).values({
    userId,
    token,
    expiresAt: sessionExpiresAt(),
  });
  return token;
}

function loginKey(reqIp: string | undefined, handle: string): string {
  return `${reqIp ?? "unknown"}:${handle}`;
}

function isLoginThrottled(key: string): boolean {
  const entry = loginFailures.get(key);
  if (!entry) return false;
  if (entry.lockedUntil <= Date.now()) {
    loginFailures.delete(key);
    return false;
  }
  return entry.count >= 5;
}

function recordLoginFailure(key: string): void {
  const entry = loginFailures.get(key);
  const count = (entry?.count ?? 0) + 1;
  const lockedUntil = count >= 5 ? Date.now() + Math.min(15 * 60 * 1000, count * 60 * 1000) : Date.now() + 60 * 1000;
  loginFailures.set(key, { count, lockedUntil });
}

function authUser(user: typeof usersTable.$inferSelect, authHandle: string, token: string, username = "sealed", primaryCode: string | null = null) {
  return {
    token,
    authHandle,
    user: {
      id: user.id,
      username,
      primaryCode,
      displayName: user.displayName,
      avatarColor: user.avatarColor,
      kemPublicKey: user.kemPublicKey,
      dsaPublicKey: user.dsaPublicKey,
      createdAt: user.createdAt,
    },
  };
}

router.post("/auth/register", async (req, res) => {
  const parse = PostAuthRegisterBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { passcode, primaryCode, displayName, kemPublicKey, dsaPublicKey, leadEmail } = parse.data;
  const normalizedPrimaryCode = primaryCode ? normalizeIdentityCode(primaryCode) : "";

  if (!isValidIdentityCode(normalizedPrimaryCode)) {
    res.status(400).json({ error: "Handle must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }

  const existing = await db
    .select({ id: identityCodesTable.id })
    .from(identityCodesTable)
    .where(eq(identityCodesTable.code, normalizedPrimaryCode))
    .limit(1);

  if (existing.length > 0) {
    res.status(409).json({ error: "Handle already claimed" });
    return;
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

  await db.insert(deviceCredentialsTable).values({
    userId: user.id,
    authHandleHash: hashAuthHandle(authHandle),
    passwordHash,
    label: "First device",
  });

  await db.insert(identityCodesTable).values({
    ownerUserId: user.id,
    code: normalizedPrimaryCode,
    kind: "alias",
  });

  const token = await createSession(user.id);

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

  res.status(201).json(authUser(user, authHandle, token, normalizedPrimaryCode, normalizedPrimaryCode));
});

router.post("/auth/passkey/register/options", async (req, res) => {
  const handle = typeof req.body?.handle === "string" ? normalizeIdentityCode(req.body.handle) : "";
  if (!isValidIdentityCode(handle)) {
    res.status(400).json({ error: "Handle must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }

  const existing = await db
    .select({ id: identityCodesTable.id })
    .from(identityCodesTable)
    .where(eq(identityCodesTable.code, handle))
    .limit(1);

  if (existing.length > 0) {
    res.status(409).json({ error: "Handle already claimed" });
    return;
  }

  const options = await generateRegistrationOptions({
    rpName: "QuantumShield",
    rpID: rpId(req),
    userName: handle,
    userID: randomBytes(16),
    userDisplayName: handle,
    attestationType: "none",
    authenticatorSelection: {
      residentKey: "required",
      userVerification: "required",
    },
    preferredAuthenticatorType: "localDevice",
  });

  rememberChallenge(options.challenge, handle);
  res.json(options);
});

router.post("/auth/passkey/register/verify", async (req, res) => {
  const body = req.body as {
    handle?: unknown;
    response?: unknown;
    kemPublicKey?: unknown;
    dsaPublicKey?: unknown;
    displayName?: unknown;
    leadEmail?: unknown;
  };
  const handle = typeof body.handle === "string" ? normalizeIdentityCode(body.handle) : "";

  if (!isValidIdentityCode(handle)) {
    res.status(400).json({ error: "Handle must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }
  if (!isRegistrationResponse(body.response) || typeof body.kemPublicKey !== "string" || typeof body.dsaPublicKey !== "string") {
    res.status(400).json({ error: "Passkey registration response and public keys are required" });
    return;
  }

  const challenge = body.response.response.clientDataJSON ? JSON.parse(Buffer.from(body.response.response.clientDataJSON, "base64url").toString("utf8")).challenge as string : "";
  if (!consumeChallenge(challenge, handle)) {
    res.status(400).json({ error: "Passkey challenge expired. Try again." });
    return;
  }

  const existing = await db
    .select({ id: identityCodesTable.id })
    .from(identityCodesTable)
    .where(eq(identityCodesTable.code, handle))
    .limit(1);

  if (existing.length > 0) {
    res.status(409).json({ error: "Handle already claimed" });
    return;
  }

  const verification = await verifyRegistrationResponse({
    response: body.response,
    expectedChallenge: challenge,
    expectedOrigin: publicOrigin(req),
    expectedRPID: rpId(req),
    requireUserVerification: true,
  });

  if (!verification.verified) {
    res.status(400).json({ error: "Passkey registration was not verified" });
    return;
  }

  const { credential } = verification.registrationInfo;
  const authHandle = generateAuthHandle();
  const [user] = await db
    .insert(usersTable)
    .values({
      username: generateInternalUsername(),
      authHandleHash: hashAuthHandle(authHandle),
      passwordHash: await argon2.hash(randomBytes(32).toString("base64url")),
      displayName: typeof body.displayName === "string" ? body.displayName : null,
      avatarColor: randomColor(),
      kemPublicKey: body.kemPublicKey,
      dsaPublicKey: body.dsaPublicKey,
    })
    .returning();

  await db.insert(deviceCredentialsTable).values({
    userId: user.id,
    authHandleHash: hashAuthHandle(authHandle),
    passwordHash: await argon2.hash(randomBytes(32).toString("base64url")),
    credentialId: credential.id,
    credentialPublicKey: Buffer.from(credential.publicKey).toString("base64url"),
    credentialCounter: credential.counter,
    credentialTransports: body.response.response.transports ?? null,
    label: "Passkey",
  });

  await db.insert(identityCodesTable).values({
    ownerUserId: user.id,
    code: handle,
    kind: "alias",
  });

  const token = await createSession(user.id);

  if (typeof body.leadEmail === "string" && body.leadEmail) {
    await db
      .insert(leadsTable)
      .values({
        email: body.leadEmail.trim().toLowerCase(),
        name: typeof body.displayName === "string" ? body.displayName : null,
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
          name: typeof body.displayName === "string" ? body.displayName : null,
          updatedAt: new Date(),
        },
      });
  }

  res.status(201).json(authUser(user, authHandle, token, handle, handle));
});

router.post("/auth/passkey/login/options", async (req, res) => {
  const handle = typeof req.body?.handle === "string" ? normalizeIdentityCode(req.body.handle) : "";
  if (!isValidIdentityCode(handle)) {
    res.status(400).json({ error: "Handle must be 2-32 letters, numbers, underscores, or dashes" });
    return;
  }

  const rows = await db
    .select({ credential: deviceCredentialsTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .innerJoin(deviceCredentialsTable, eq(deviceCredentialsTable.userId, usersTable.id))
    .where(
      and(
        eq(identityCodesTable.code, handle),
        eq(identityCodesTable.kind, "alias"),
        eq(identityCodesTable.active, true),
        isNull(deviceCredentialsTable.revokedAt),
        or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
      )
    );

  const allowCredentials = rows
    .filter(({ credential }) => credential.credentialId)
    .map(({ credential }) => ({
      id: credential.credentialId!,
      transports: (credential.credentialTransports ?? undefined) as AuthenticatorTransportFuture[] | undefined,
    }));

  if (allowCredentials.length === 0) {
    res.status(404).json({ error: "No passkey found for that handle" });
    return;
  }

  const options = await generateAuthenticationOptions({
    rpID: rpId(req),
    allowCredentials,
    userVerification: "required",
  });

  rememberChallenge(options.challenge, handle);
  res.json(options);
});

router.post("/auth/passkey/login/verify", async (req, res) => {
  const body = req.body as { handle?: unknown; response?: unknown };
  const handle = typeof body.handle === "string" ? normalizeIdentityCode(body.handle) : "";
  if (!isValidIdentityCode(handle) || !isAuthenticationResponse(body.response)) {
    res.status(400).json({ error: "Handle and passkey response are required" });
    return;
  }

  const challenge = body.response.response.clientDataJSON ? JSON.parse(Buffer.from(body.response.response.clientDataJSON, "base64url").toString("utf8")).challenge as string : "";
  if (!consumeChallenge(challenge, handle)) {
    res.status(400).json({ error: "Passkey challenge expired. Try again." });
    return;
  }

  const [row] = await db
    .select({ code: identityCodesTable, user: usersTable, credential: deviceCredentialsTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .innerJoin(deviceCredentialsTable, eq(deviceCredentialsTable.userId, usersTable.id))
    .where(
      and(
        eq(identityCodesTable.code, handle),
        eq(identityCodesTable.kind, "alias"),
        eq(identityCodesTable.active, true),
        eq(deviceCredentialsTable.credentialId, body.response.id),
        isNull(deviceCredentialsTable.revokedAt),
        or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
      )
    )
    .limit(1);

  if (!row || !row.credential.credentialId || !row.credential.credentialPublicKey) {
    res.status(401).json({ error: "Invalid handle or passkey" });
    return;
  }

  const verification = await verifyAuthenticationResponse({
    response: body.response,
    expectedChallenge: challenge,
    expectedOrigin: publicOrigin(req),
    expectedRPID: rpId(req),
    credential: {
      id: row.credential.credentialId,
      publicKey: Buffer.from(row.credential.credentialPublicKey, "base64url"),
      counter: row.credential.credentialCounter,
      transports: (row.credential.credentialTransports ?? undefined) as AuthenticatorTransportFuture[] | undefined,
    },
    requireUserVerification: true,
  });

  if (!verification.verified) {
    res.status(401).json({ error: "Invalid handle or passkey" });
    return;
  }

  await db
    .update(deviceCredentialsTable)
    .set({ credentialCounter: verification.authenticationInfo.newCounter })
    .where(eq(deviceCredentialsTable.id, row.credential.id));

  const token = await createSession(row.user.id);
  res.json(authUser(row.user, generateAuthHandle(), token, handle, handle));
});

router.post("/auth/login", async (req, res) => {
  const parse = PostAuthLoginBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { handle, passcode } = parse.data;
  const normalizedHandle = normalizeIdentityCode(handle);
  const throttleKey = loginKey(req.ip, normalizedHandle);

  if (isLoginThrottled(throttleKey)) {
    res.status(429).json({ error: "Too many login attempts. Try again later." });
    return;
  }

  const [row] = await db
    .select({ code: identityCodesTable, user: usersTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .where(
      and(
        eq(identityCodesTable.code, normalizedHandle),
        eq(identityCodesTable.kind, "alias"),
        eq(identityCodesTable.active, true),
        or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
      )
    )
    .limit(1);

  const user = row?.user;
  const passwordHash = user?.passwordHash;

  if (!user || !passwordHash) {
    recordLoginFailure(throttleKey);
    res.status(401).json({ error: "Invalid handle or passcode" });
    return;
  }

  const valid = await argon2.verify(passwordHash, passcode);
  if (!valid) {
    recordLoginFailure(throttleKey);
    res.status(401).json({ error: "Invalid handle or passcode" });
    return;
  }

  loginFailures.delete(throttleKey);
  const token = await createSession(user.id);
  res.json(authUser(user, generateAuthHandle(), token, normalizedHandle, normalizedHandle));
});

router.post("/auth/link-device", async (req, res) => {
  const body = req.body as { code?: unknown; passcode?: unknown; deviceLabel?: unknown };
  if (typeof body.code !== "string" || body.code.length < 2 || body.code.length > 32) {
    res.status(400).json({ error: "Code must be 2-32 characters" });
    return;
  }
  if (typeof body.passcode !== "string" || body.passcode.length < 8) {
    res.status(400).json({ error: "Device passcode is required" });
    return;
  }
  if (body.deviceLabel !== undefined && body.deviceLabel !== null && typeof body.deviceLabel !== "string") {
    res.status(400).json({ error: "Device label must be a string" });
    return;
  }

  const requestedCode = normalizeIdentityCode(body.code);
  const [row] = await db
    .select({ code: identityCodesTable, user: usersTable })
    .from(identityCodesTable)
    .innerJoin(usersTable, eq(identityCodesTable.ownerUserId, usersTable.id))
    .where(
      and(
        eq(identityCodesTable.code, requestedCode),
        eq(identityCodesTable.active, true),
        or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))
      )
    )
    .limit(1);

  if (!row) {
    res.status(404).json({ error: "Code is not active or has expired" });
    return;
  }

  if (row.code.kind !== "invite") {
    res.status(403).json({ error: "Device linking requires an invite code. Handles are for discovery only." });
    return;
  }

  if (row.code.maxUses !== null && row.code.useCount >= row.code.maxUses) {
    res.status(403).json({ error: "Code has reached its use limit" });
    return;
  }

  const authHandle = generateAuthHandle();
  await db.insert(deviceCredentialsTable).values({
    userId: row.user.id,
    authHandleHash: hashAuthHandle(authHandle),
    passwordHash: await argon2.hash(body.passcode),
    label: body.deviceLabel ?? "Linked device",
    linkedByCode: row.code.code,
  });

  await db
    .update(identityCodesTable)
    .set({
      useCount: row.code.useCount + 1,
      expiresAt: row.code.kind === "invite" && row.code.maxUses === 1 ? expiryFromTtl(1) : row.code.expiresAt,
      updatedAt: new Date(),
    })
    .where(eq(identityCodesTable.id, row.code.id));

  const token = await createSession(row.user.id);
  void notifyUser(row.user.id, {
    title: "New device linked",
    body: `A new device was linked with invite ${row.code.code}. Disable or roll the invite if this was not you.`,
    url: "/app",
    tag: "quantumshield-device-link",
  });
  res.status(201).json(authUser(row.user, authHandle, token, row.code.code, row.code.code));
});

router.get("/auth/me", requireAuth, async (req: AuthRequest, res) => {
  const u = req.user!;
  const [primary] = await db
    .select({ code: identityCodesTable.code })
    .from(identityCodesTable)
    .where(and(eq(identityCodesTable.ownerUserId, u.id), eq(identityCodesTable.kind, "alias"), eq(identityCodesTable.active, true)))
    .limit(1);

  res.json({
    id: u.id,
    username: primary?.code ?? "sealed",
    primaryCode: primary?.code ?? null,
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
