#!/usr/bin/env bash
set -euo pipefail

if [[ "${ALLOW_DB_PUSH:-}" != "1" ]]; then
  cat >&2 <<'EOF'
Refusing to run drizzle-kit push.

Set ALLOW_DB_PUSH=1 only for development databases after reviewing the
Drizzle prompt. For production, use the manual migration SQL in lib/db/migrations/manual/.
EOF
  exit 1
fi

if [[ "${NODE_ENV:-}" == "production" || "${REPLIT_ENVIRONMENT:-}" == "production" ]]; then
  cat >&2 <<'EOF'
Refusing to run drizzle-kit push in a production environment.

Use the reviewed manual migration SQL in lib/db/migrations/manual/ instead.
EOF
  exit 1
fi
