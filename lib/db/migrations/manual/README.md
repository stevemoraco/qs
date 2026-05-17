# Manual Database Migrations

Use these scripts for production or shared databases when `drizzle-kit push` reports a data-risk prompt.

`drizzle-kit push` is still useful for disposable development databases, but it can offer destructive choices such as truncating a table before adding a constraint. Do not accept truncation for production data.

## Current Pending Manual Migrations

Run this first for the durable push notification job queue:

```sh
psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_push_notification_jobs.sql
```

It creates the additive `push_notification_jobs` table and indexes used by the API push worker. It does not rewrite or truncate existing data.

Run this for durable sanitized client/server error diagnostics:

```sh
psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_error_logs.sql
```

It creates the additive `error_logs` table and indexes used by the API error handler and PWA client error reporting. It stores version/build metadata and sanitized operational details only, not request bodies, plaintext messages, ciphertext, wrapped keys, passcodes, or auth tokens.

Then run this for the `device_credentials.credential_id` unique constraint:

```sh
psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_device_credentials_credential_id_unique.sql
```

Before it changes anything, the script checks for duplicate non-null `credential_id` values and exits with an error if any exist. It then creates a unique index concurrently and attaches it as the expected constraint, avoiding table truncation.

After running it, verify with:

```sh
psql "$DATABASE_URL" -c "select conname, pg_get_constraintdef(oid) from pg_constraint where conname = 'device_credentials_credential_id_unique';"
```

Verify the push queue table with:

```sh
psql "$DATABASE_URL" -c "\d public.push_notification_jobs"
```

Verify the error log table with:

```sh
psql "$DATABASE_URL" -c "\d public.error_logs"
```
