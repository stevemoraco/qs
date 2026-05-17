import { Router } from "express";
import { db, preKeysTable, roomMembersTable, usersTable } from "@workspace/db";
import { and, desc, eq, inArray } from "drizzle-orm";
import { PostKeysUploadBody } from "@workspace/api-zod";
import { ml_dsa87 } from "@noble/post-quantum/ml-dsa.js";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();
const FRESH_SESSION_WINDOW_MS = 10 * 60 * 1000;
const ML_KEM_1024_PUBLIC_KEY_BYTES = 1568;
const ML_DSA_87_PUBLIC_KEY_BYTES = 2592;
const ML_DSA_87_SIGNATURE_BYTES = 4627;

function routeParam(value: string | string[] | undefined): string {
  return Array.isArray(value) ? value[0] : (value ?? "");
}

function base64ByteLength(value: string): number | null {
  try {
    const normalized = value.trim();
    if (!/^[A-Za-z0-9+/]+={0,2}$/.test(normalized) || normalized.length % 4 !== 0) return null;
    return Buffer.from(normalized, "base64").length;
  } catch {
    return null;
  }
}

function hasExpectedKeyBundleShape(input: { kemPublicKey: string; dsaPublicKey: string; kemSignature: string }): boolean {
  return (
    base64ByteLength(input.kemPublicKey) === ML_KEM_1024_PUBLIC_KEY_BYTES &&
    base64ByteLength(input.dsaPublicKey) === ML_DSA_87_PUBLIC_KEY_BYTES &&
    base64ByteLength(input.kemSignature) === ML_DSA_87_SIGNATURE_BYTES
  );
}

function base64Bytes(value: string): Uint8Array {
  return new Uint8Array(Buffer.from(value, "base64"));
}

function verifiesKeyBundleSignature(input: { kemPublicKey: string; dsaPublicKey: string; kemSignature: string }): boolean {
  try {
    return ml_dsa87.verify(
      base64Bytes(input.kemSignature),
      base64Bytes(input.kemPublicKey),
      base64Bytes(input.dsaPublicKey),
    );
  } catch {
    return false;
  }
}

function hasFreshSession(req: AuthRequest): boolean {
  return !!req.sessionCreatedAt && Date.now() - req.sessionCreatedAt.getTime() <= FRESH_SESSION_WINDOW_MS;
}

async function canReadKeyBundle(requesterId: string, targetUserId: string): Promise<boolean> {
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

router.post("/keys/upload", requireAuth, async (req: AuthRequest, res) => {
  const parse = PostKeysUploadBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { kemPublicKey, dsaPublicKey, kemSignature } = parse.data;
  const nextBundle = { kemPublicKey, dsaPublicKey, kemSignature };
  if (!hasExpectedKeyBundleShape(nextBundle)) {
    res.status(400).json({ error: "Invalid ML-KEM/ML-DSA key bundle shape" });
    return;
  }
  if (!verifiesKeyBundleSignature(nextBundle)) {
    res.status(400).json({ error: "Invalid ML-DSA key bundle signature" });
    return;
  }

  const [currentUser] = await db
    .select({ kemPublicKey: usersTable.kemPublicKey, dsaPublicKey: usersTable.dsaPublicKey })
    .from(usersTable)
    .where(eq(usersTable.id, req.userId!))
    .limit(1);

  if (!currentUser) {
    res.status(401).json({ error: "Unauthorized" });
    return;
  }

  const hasCurrentBundle = !!currentUser.kemPublicKey && !!currentUser.dsaPublicKey;
  const sameKem = currentUser.kemPublicKey === kemPublicKey;
  const sameDsa = currentUser.dsaPublicKey === dsaPublicKey;
  const replacingIdentityKey = hasCurrentBundle && !sameDsa;
  if (replacingIdentityKey && !hasFreshSession(req)) {
    res.status(409).json({ error: "Replacing the account signing key requires a fresh device verification." });
    return;
  }

  if (hasCurrentBundle && sameKem && sameDsa) {
    const [latest] = await db
      .select({ kemPublicKey: preKeysTable.kemPublicKey, dsaPublicKey: preKeysTable.dsaPublicKey, kemSignature: preKeysTable.kemSignature })
      .from(preKeysTable)
      .where(eq(preKeysTable.userId, req.userId!))
      .orderBy(desc(preKeysTable.createdAt))
      .limit(1);
    if (latest?.kemPublicKey === kemPublicKey && latest.dsaPublicKey === dsaPublicKey && latest.kemSignature === kemSignature) {
      res.json({ ok: true });
      return;
    }
  }

  await db
    .update(usersTable)
    .set({ kemPublicKey, dsaPublicKey })
    .where(eq(usersTable.id, req.userId!));

  await db
    .insert(preKeysTable)
    .values({ userId: req.userId!, kemPublicKey, dsaPublicKey, kemSignature });

  res.json({ ok: true });
});

router.get("/keys/:userId", requireAuth, async (req: AuthRequest, res) => {
  const userId = routeParam(req.params.userId);

  if (!(await canReadKeyBundle(req.userId!, userId))) {
    res.status(404).json({ error: "No pre-key bundle found for this user" });
    return;
  }

  const [key] = await db
    .select()
    .from(preKeysTable)
    .where(eq(preKeysTable.userId, userId))
    .orderBy(desc(preKeysTable.createdAt))
    .limit(1);

  if (!key) {
    res.status(404).json({ error: "No pre-key bundle found for this user" });
    return;
  }

  res.json({
    kemPublicKey: key.kemPublicKey,
    dsaPublicKey: key.dsaPublicKey,
    kemSignature: key.kemSignature,
    oneTimePreKeys: null,
  });
});

router.get("/keys/:userId/devices", requireAuth, async (req: AuthRequest, res) => {
  const userId = routeParam(req.params.userId);

  if (!(await canReadKeyBundle(req.userId!, userId))) {
    res.status(404).json({ error: "No pre-key bundles found for this user" });
    return;
  }

  const rows = await db
    .select()
    .from(preKeysTable)
    .where(eq(preKeysTable.userId, userId))
    .orderBy(desc(preKeysTable.createdAt));

  const seenKemKeys = new Set<string>();
  const bundles = rows
    .filter((key) => {
      if (seenKemKeys.has(key.kemPublicKey)) return false;
      seenKemKeys.add(key.kemPublicKey);
      return true;
    })
    .map((key) => ({
      kemPublicKey: key.kemPublicKey,
      dsaPublicKey: key.dsaPublicKey,
      kemSignature: key.kemSignature,
      oneTimePreKeys: null,
    }));

  if (bundles.length === 0) {
    res.status(404).json({ error: "No pre-key bundles found for this user" });
    return;
  }

  res.json({ bundles });
});

export default router;
