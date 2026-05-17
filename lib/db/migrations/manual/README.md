# Manual Database Migrations

Use these scripts for production or shared databases when `drizzle-kit push` reports a data-risk prompt.

`drizzle-kit push` is still useful for disposable development databases, but it can offer destructive choices such as truncating a table before adding a constraint. Do not accept truncation for production data.

## Current Pending Manual Migration

Run this for the `device_credentials.credential_id` unique constraint:

```sh
psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_device_credentials_credential_id_unique.sql
```

Before it changes anything, the script checks for duplicate non-null `credential_id` values and exits with an error if any exist. It then creates a unique index concurrently and attaches it as the expected constraint, avoiding table truncation.

After running it, verify with:

```sh
psql "$DATABASE_URL" -c "select conname, pg_get_constraintdef(oid) from pg_constraint where conname = 'device_credentials_credential_id_unique';"
```
