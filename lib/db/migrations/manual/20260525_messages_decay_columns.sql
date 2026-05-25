-- Adds the decay/availability columns to public.messages to match the
-- Drizzle schema in lib/db/src/schema/messages.ts.
--
-- Run with:
--   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260525_messages_decay_columns.sql
--
-- This migration is additive. `available_at` is added without a default first,
-- backfilled from `created_at` so historical rows reflect their original
-- availability time, then set NOT NULL with default now() for future inserts.

alter table public.messages
  add column if not exists decay_attestation jsonb,
  add column if not exists decayed_at timestamptz,
  add column if not exists sender_dsa_public_key text;

alter table public.messages
  add column if not exists available_at timestamptz;

update public.messages
  set available_at = created_at
  where available_at is null;

alter table public.messages
  alter column available_at set default now();

alter table public.messages
  alter column available_at set not null;
