-- Creates the durable sanitized error log table used for post-deploy
-- diagnostics. This migration is additive and does not rewrite or truncate data.
--
-- Run with:
--   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_error_logs.sql

create table if not exists public.error_logs (
  id uuid primary key default gen_random_uuid(),
  source text not null,
  level text not null default 'error',
  code text,
  message text not null,
  method text,
  path text,
  status_code integer,
  user_id uuid references public.users(id) on delete set null,
  client_commit text,
  client_version text,
  server_commit text,
  server_version text,
  server_started_at timestamptz,
  details jsonb,
  created_at timestamptz not null default now()
);

create index concurrently if not exists error_logs_created_at_idx
  on public.error_logs (created_at desc);

create index concurrently if not exists error_logs_code_created_at_idx
  on public.error_logs (code, created_at desc);

create index concurrently if not exists error_logs_user_id_created_at_idx
  on public.error_logs (user_id, created_at desc)
  where user_id is not null;
