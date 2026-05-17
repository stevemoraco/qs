import { integer, jsonb, pgTable, text, timestamp, uuid } from "drizzle-orm/pg-core";
import { usersTable } from "./users";

export const errorLogsTable = pgTable("error_logs", {
  id: uuid("id").primaryKey().defaultRandom(),
  source: text("source").notNull(),
  level: text("level").notNull().default("error"),
  code: text("code"),
  message: text("message").notNull(),
  method: text("method"),
  path: text("path"),
  statusCode: integer("status_code"),
  userId: uuid("user_id").references(() => usersTable.id, { onDelete: "set null" }),
  clientCommit: text("client_commit"),
  clientVersion: text("client_version"),
  serverCommit: text("server_commit"),
  serverVersion: text("server_version"),
  serverStartedAt: timestamp("server_started_at", { withTimezone: true }),
  details: jsonb("details"),
  createdAt: timestamp("created_at", { withTimezone: true }).defaultNow().notNull(),
});

export type ErrorLog = typeof errorLogsTable.$inferSelect;
