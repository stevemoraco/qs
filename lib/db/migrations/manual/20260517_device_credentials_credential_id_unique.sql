-- Adds the unique constraint expected by the Drizzle schema without truncating data.
--
-- Run with:
--   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_device_credentials_credential_id_unique.sql
--
-- This migration intentionally avoids `drizzle-kit push` because Drizzle prompts to
-- truncate device_credentials when adding this constraint to a non-empty table.

\set constraint_name device_credentials_credential_id_unique

select case when exists (
  select 1
  from pg_constraint c
  join pg_class t on t.oid = c.conrelid
  join pg_namespace n on n.oid = t.relnamespace
  where n.nspname = 'public'
    and t.relname = 'device_credentials'
    and c.conname = :'constraint_name'
) then 'true' else 'false' end as constraint_exists
\gset

\if :constraint_exists
  \echo 'Constraint already exists; no migration needed.'
\else
  do $$
  begin
    if exists (
      select 1
      from (
        select credential_id
        from public.device_credentials
        where credential_id is not null
        group by credential_id
        having count(*) > 1
      ) duplicates
    ) then
      raise exception 'Cannot add device_credentials_credential_id_unique: duplicate credential_id values exist.';
    end if;
  end
  $$;

  create unique index concurrently if not exists device_credentials_credential_id_unique_idx
    on public.device_credentials (credential_id);

  alter table public.device_credentials
    add constraint device_credentials_credential_id_unique
    unique using index device_credentials_credential_id_unique_idx;
\endif
