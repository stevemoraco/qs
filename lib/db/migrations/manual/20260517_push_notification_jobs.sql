-- Creates the durable push notification job queue used for fuzz-delayed
-- delivery. This migration is additive and does not rewrite or truncate data.
--
-- Run with:
--   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_push_notification_jobs.sql

create table if not exists public.push_notification_jobs (
  id uuid primary key default gen_random_uuid(),
  user_id uuid not null references public.users(id) on delete cascade,
  payload jsonb not null,
  due_at timestamptz not null,
  processed_at timestamptz,
  locked_at timestamptz,
  attempts integer not null default 0,
  last_error text,
  created_at timestamptz not null default now()
);

create index concurrently if not exists push_notification_jobs_due_unprocessed_idx
  on public.push_notification_jobs (due_at)
  where processed_at is null;

create index concurrently if not exists push_notification_jobs_user_id_idx
  on public.push_notification_jobs (user_id);
