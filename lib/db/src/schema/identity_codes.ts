import { boolean, integer, jsonb, pgTable, text, timestamp, uuid } from "drizzle-orm/pg-core";
import { usersTable } from "./users";

export const identityCodesTable = pgTable("identity_codes", {
  id: uuid("id").primaryKey().defaultRandom(),
  ownerUserId: uuid("owner_user_id")
    .notNull()
    .references(() => usersTable.id, { onDelete: "cascade" }),
  code: text("code").notNull().unique(),
  kind: text("kind").notNull().default("alias"),
  visibilityScope: text("visibility_scope").notNull().default("public"),
  active: boolean("active").notNull().default(true),
  maxUses: integer("max_uses"),
  useCount: integer("use_count").notNull().default(0),
  allowedCodes: jsonb("allowed_codes").$type<string[] | null>(),
  expiresAt: timestamp("expires_at", { withTimezone: true }),
  rolledAt: timestamp("rolled_at", { withTimezone: true }),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
  updatedAt: timestamp("updated_at", { withTimezone: true }).defaultNow().notNull(),
});

export type IdentityCode = typeof identityCodesTable.$inferSelect;
