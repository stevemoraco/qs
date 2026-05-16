import { integer, jsonb, pgTable, text, timestamp, uuid } from "drizzle-orm/pg-core";
import { usersTable } from "./users";

export const deviceCredentialsTable = pgTable("device_credentials", {
  id: uuid("id").primaryKey().defaultRandom(),
  userId: uuid("user_id")
    .notNull()
    .references(() => usersTable.id, { onDelete: "cascade" }),
  authHandleHash: text("auth_handle_hash").notNull().unique(),
  passwordHash: text("password_hash").notNull(),
  credentialId: text("credential_id").unique(),
  credentialPublicKey: text("credential_public_key"),
  credentialCounter: integer("credential_counter").notNull().default(0),
  credentialTransports: jsonb("credential_transports").$type<string[] | null>(),
  label: text("label"),
  linkedByCode: text("linked_by_code"),
  revokedAt: timestamp("revoked_at", { withTimezone: true }),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
});

export type DeviceCredential = typeof deviceCredentialsTable.$inferSelect;
