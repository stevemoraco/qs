-- Adds the delivery_fuzz_seconds and decay_mode columns to public.rooms to
-- match the Drizzle schema in lib/db/src/schema/rooms.ts.
--
-- Run with:
--   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260525_rooms_delivery_columns.sql
--
-- This migration is additive. Existing rows get the column defaults
-- (delivery_fuzz_seconds = 89, decay_mode = 'standard').

alter table public.rooms
  add column if not exists delivery_fuzz_seconds integer not null default 89;

alter table public.rooms
  add column if not exists decay_mode text not null default 'standard';
