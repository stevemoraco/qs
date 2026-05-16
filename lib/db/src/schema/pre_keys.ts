import { pgTable, text, timestamp, uuid } from "drizzle-orm/pg-core";
import { usersTable } from "./users";

export const preKeysTable = pgTable("pre_keys", {
  id: uuid("id").primaryKey().defaultRandom(),
  userId: uuid("user_id")
    .notNull()
    .references(() => usersTable.id, { onDelete: "cascade" }),
  kemPublicKey: text("kem_public_key").notNull(),
  dsaPublicKey: text("dsa_public_key").notNull(),
  kemSignature: text("kem_signature").notNull(),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
});

export type PreKey = typeof preKeysTable.$inferSelect;
