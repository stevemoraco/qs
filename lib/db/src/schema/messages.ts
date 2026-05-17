import { pgTable, text, timestamp, uuid, jsonb } from "drizzle-orm/pg-core";
import { usersTable } from "./users";
import { roomsTable } from "./rooms";

export const messagesTable = pgTable("messages", {
  id: uuid("id").primaryKey().defaultRandom(),
  roomId: uuid("room_id")
    .notNull()
    .references(() => roomsTable.id, { onDelete: "cascade" }),
  senderId: uuid("sender_id")
    .notNull()
    .references(() => usersTable.id, { onDelete: "cascade" }),
  ciphertext: text("ciphertext").notNull(),
  nonce: text("nonce").notNull(),
  algorithm: text("algorithm").notNull().default("AES-256-GCM+ML-KEM-1024+ML-DSA-87"),
  signature: text("signature"),
  recipientEncryptedKeys: jsonb("recipient_encrypted_keys"),
  expiresAt: timestamp("expires_at", { withTimezone: true }),
  availableAt: timestamp("available_at", { withTimezone: true }).defaultNow().notNull(),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
});

export type Message = typeof messagesTable.$inferSelect;
