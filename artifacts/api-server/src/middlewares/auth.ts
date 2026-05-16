import { type Request, type Response, type NextFunction } from "express";
import { db, sessionsTable, usersTable } from "@workspace/db";
import { eq, and, gt } from "drizzle-orm";

const SESSION_EXTENSION_DAYS = 30;
const SESSION_REFRESH_WINDOW_DAYS = 7;

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
        eq(sessionsTable.token, token),
        gt(sessionsTable.expiresAt, new Date())
      )
    )
    .limit(1);

  if (!session) {
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

  const refreshAt = Date.now() + SESSION_REFRESH_WINDOW_DAYS * 24 * 60 * 60 * 1000;
  if (session.expiresAt.getTime() < refreshAt) {
    const expiresAt = new Date();
    expiresAt.setDate(expiresAt.getDate() + SESSION_EXTENSION_DAYS);
    await db
      .update(sessionsTable)
      .set({ expiresAt })
      .where(eq(sessionsTable.token, token));
  }

  req.userId = user.id;
  req.sessionCreatedAt = session.createdAt;
  req.user = user;
  next();
}
