import { pgTable, timestamp, uuid, primaryKey } from "drizzle-orm/pg-core";
import { usersTable } from "./users";
import { roomsTable } from "./rooms";

export const roomMembersTable = pgTable(
  "room_members",
  {
    roomId: uuid("room_id")
      .notNull()
      .references(() => roomsTable.id, { onDelete: "cascade" }),
    userId: uuid("user_id")
      .notNull()
      .references(() => usersTable.id, { onDelete: "cascade" }),
    joinedAt: timestamp("joined_at", { withTimezone: true }).defaultNow().notNull(),
  },
  (t) => [primaryKey({ columns: [t.roomId, t.userId] })]
);

export type RoomMember = typeof roomMembersTable.$inferSelect;
