# Manual Database Migrations

Use these scripts for production or shared databases when `drizzle-kit push` reports a data-risk prompt.

`drizzle-kit push` is still useful for disposable development databases, but it can offer destructive choices such as truncating a table before adding a constraint. Do not accept truncation for production data.

## Current Pending Manual Migrations

Run these in order. All scripts are idempotent (safe to re-run) and additive (no data rewrite or truncation).

1. Durable push notification job queue:

   ```sh
   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_push_notification_jobs.sql
   ```

   Creates the `push_notification_jobs` table and indexes used by the API push worker.

2. Durable sanitized client/server error diagnostics:

   ```sh
   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_error_logs.sql
   ```

   Creates the `error_logs` table and indexes used by the API error handler and PWA client error reporting. Stores version/build metadata and sanitized operational details only — not request bodies, plaintext messages, ciphertext, wrapped keys, passcodes, or auth tokens.

3. Room delivery-fuzz and decay-mode columns:

   ```sh
   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260525_rooms_delivery_columns.sql
   ```

   Adds `rooms.delivery_fuzz_seconds` (default 89) and `rooms.decay_mode` (default `'standard'`). Existing rows are backfilled by the column defaults.

4. Message decay/availability columns:

   ```sh
   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260525_messages_decay_columns.sql
   ```

   Adds `messages.available_at`, `messages.decay_attestation`, `messages.decayed_at`, and `messages.sender_dsa_public_key`. `available_at` is backfilled from `created_at` for existing rows before being set `NOT NULL DEFAULT now()`, so historical messages keep their original availability time.

5. Drop the legacy partial unique index on `device_credentials.credential_id`:

   ```sh
   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260525_device_credentials_drop_partial_index.sql
   ```

   Some environments have a legacy `CREATE UNIQUE INDEX ... WHERE credential_id IS NOT NULL` named `device_credentials_credential_id_unique` (an index, not a constraint). Step 6 needs that name available to attach a UNIQUE *constraint* of the same name. This script no-ops if the legacy index isn't there or is already attached to a constraint.

6. `device_credentials.credential_id` UNIQUE constraint:

   ```sh
   psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -f lib/db/migrations/manual/20260517_device_credentials_credential_id_unique.sql
   ```

   Checks for duplicate non-null `credential_id` values first and exits with an error if any exist. Then creates a unique index concurrently and attaches it as the expected constraint, avoiding table truncation.

### Verification

```sh
psql "$DATABASE_URL" -c "\d public.push_notification_jobs"
psql "$DATABASE_URL" -c "\d public.error_logs"
psql "$DATABASE_URL" -c "\d public.rooms"
psql "$DATABASE_URL" -c "\d public.messages"
psql "$DATABASE_URL" -c "select conname, pg_get_constraintdef(oid) from pg_constraint where conname = 'device_credentials_credential_id_unique';"
```
