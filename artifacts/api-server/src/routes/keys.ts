import { Router } from "express";
import { db, preKeysTable, usersTable } from "@workspace/db";
import { eq } from "drizzle-orm";
import { PostKeysUploadBody } from "@workspace/api-zod";
import { requireAuth, type AuthRequest } from "../middlewares/auth";

const router = Router();

router.post("/keys/upload", requireAuth, async (req: AuthRequest, res) => {
  const parse = PostKeysUploadBody.safeParse(req.body);
  if (!parse.success) {
    res.status(400).json({ error: parse.error.message });
    return;
  }

  const { kemPublicKey, dsaPublicKey, kemSignature } = parse.data;

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
  const [key] = await db
    .select()
    .from(preKeysTable)
    .where(eq(preKeysTable.userId, req.params.userId))
    .orderBy(preKeysTable.createdAt)
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

export default router;
