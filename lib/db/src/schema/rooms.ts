import { pgTable, text, timestamp, uuid, integer } from "drizzle-orm/pg-core";

export const roomsTable = pgTable("rooms", {
  id: uuid("id").primaryKey().defaultRandom(),
  name: text("name"),
  type: text("type", { enum: ["direct", "group"] }).notNull().default("direct"),
  ttlSeconds: integer("ttl_seconds"),
  ttlMode: text("ttl_mode", { enum: ["after_view", "after_send"] }).notNull().default("after_view"),
  deliveryFuzzSeconds: integer("delivery_fuzz_seconds").notNull().default(89),
  decayMode: text("decay_mode", { enum: ["standard", "experimental_quorum_decay"] }).notNull().default("standard"),
  lastMessageAt: timestamp("last_message_at", { withTimezone: true }),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
});

export type Room = typeof roomsTable.$inferSelect;
