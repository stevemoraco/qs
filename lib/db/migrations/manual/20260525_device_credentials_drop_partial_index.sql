-- Drops the legacy partial unique index named device_credentials_credential_id_unique
-- so that 20260517_device_credentials_credential_id_unique.sql can attach a full
-- UNIQUE constraint with the same name afterwards.
--
-- Run with:
--   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260525_device_credentials_drop_partial_index.sql
--
-- Background: an earlier deploy created
--   CREATE UNIQUE INDEX device_credentials_credential_id_unique
--     ON public.device_credentials (credential_id) WHERE (credential_id IS NOT NULL);
-- The Drizzle schema expects a UNIQUE *constraint* of the same name. A full
-- UNIQUE constraint on a nullable column allows multiple NULLs (NULL is distinct
-- from NULL by default), so this is functionally equivalent for uniqueness but
-- makes the index usable as an ON CONFLICT target and matches the catalog
-- shape Drizzle introspects.

-- 1) Decide whether the legacy plain INDEX still exists (i.e. not yet attached
--    to a CONSTRAINT). DROP INDEX CONCURRENTLY can't run inside a transaction
--    or a DO block, so we use psql \gset + \if to branch.
select case when exists (
  select 1
  from pg_index i
  join pg_class c on c.oid = i.indexrelid
  join pg_namespace n on n.oid = c.relnamespace
  where n.nspname = 'public'
    and c.relname = 'device_credentials_credential_id_unique'
    and not exists (
      select 1 from pg_constraint k
      where k.conname = 'device_credentials_credential_id_unique'
    )
) then 'true' else 'false' end as legacy_index_present
\gset

\if :legacy_index_present
  drop index concurrently public.device_credentials_credential_id_unique;
\else
  \echo 'Legacy partial index not present (or already backing a constraint); nothing to drop.'
\endif
