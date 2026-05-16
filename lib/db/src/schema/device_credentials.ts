import { pgTable, text, timestamp, uuid } from "drizzle-orm/pg-core";
import { usersTable } from "./users";

export const deviceCredentialsTable = pgTable("device_credentials", {
  id: uuid("id").primaryKey().defaultRandom(),
  userId: uuid("user_id")
    .notNull()
    .references(() => usersTable.id, { onDelete: "cascade" }),
  authHandleHash: text("auth_handle_hash").notNull().unique(),
  passwordHash: text("password_hash").notNull(),
  label: text("label"),
  linkedByCode: text("linked_by_code"),
  revokedAt: timestamp("revoked_at", { withTimezone: true }),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
});

export type DeviceCredential = typeof deviceCredentialsTable.$inferSelect;
