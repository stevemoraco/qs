import { type Request, type Response, type NextFunction } from "express";
import { db, sessionsTable, usersTable } from "@workspace/db";
import { eq, and, gt, inArray } from "drizzle-orm";
import { hashSessionToken, sessionTokenLookupValues } from "../lib/session-token";

const SESSION_DURATION_MS = 60 * 60 * 1000;

export interface AuthRequest extends Request {
  userId?: string;
  sessionCreatedAt?: Date;
  user?: {
    id: string;
    username: string;
    displayName: string | null;
    avatarColor: string | null;
    kemPublicKey: string | null;
    dsaPublicKey: string | null;
    createdAt: Date;
  };
}

export async function requireAuth(
  req: AuthRequest,
  res: Response,
  next: NextFunction
): Promise<void> {
  const authHeader = req.headers.authorization;
  if (!authHeader?.startsWith("Bearer ")) {
    res.status(401).json({ error: "Unauthorized" });
    return;
  }

  const token = authHeader.slice(7);

  const [session] = await db
    .select({
      userId: sessionsTable.userId,
      expiresAt: sessionsTable.expiresAt,
      createdAt: sessionsTable.createdAt,
    })
    .from(sessionsTable)
    .where(
      and(
        inArray(sessionsTable.token, sessionTokenLookupValues(token)),
        gt(sessionsTable.expiresAt, new Date())
      )
    )
    .limit(1);

  if (!session) {
    res.status(401).json({ error: "Unauthorized" });
    return;
  }

  const absoluteExpiresAt = session.createdAt.getTime() + SESSION_DURATION_MS;
  if (absoluteExpiresAt <= Date.now()) {
    await db.delete(sessionsTable).where(inArray(sessionsTable.token, sessionTokenLookupValues(token)));
    res.status(401).json({ error: "Unauthorized" });
    return;
  }

  const [user] = await db
    .select()
    .from(usersTable)
    .where(eq(usersTable.id, session.userId))
    .limit(1);

  if (!user) {
    res.status(401).json({ error: "Unauthorized" });
    return;
  }

  req.userId = user.id;
  req.sessionCreatedAt = session.createdAt;
  req.user = user;
  next();
}
