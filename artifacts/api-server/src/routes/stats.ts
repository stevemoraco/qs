import { Router } from "express";
import { db, usersTable, roomsTable, messagesTable } from "@workspace/db";
import { count, gte } from "drizzle-orm";
import { requireAuth } from "../middlewares/auth";

const router = Router();

router.get("/stats/overview", requireAuth, async (_req, res) => {
  const [{ totalUsers }] = await db
    .select({ totalUsers: count() })
    .from(usersTable);

  const [{ totalRooms }] = await db
    .select({ totalRooms: count() })
    .from(roomsTable);

  const [{ totalMessages }] = await db
    .select({ totalMessages: count() })
    .from(messagesTable);

  const today = new Date();
  today.setHours(0, 0, 0, 0);

  const [{ activeRoomsToday }] = await db
    .select({ activeRoomsToday: count() })
    .from(messagesTable)
    .where(gte(messagesTable.createdAt, today));

  res.json({
    totalUsers: Number(totalUsers),
    totalRooms: Number(totalRooms),
    totalMessages: Number(totalMessages),
    activeRoomsToday: Number(activeRoomsToday),
  });
});

export default router;
