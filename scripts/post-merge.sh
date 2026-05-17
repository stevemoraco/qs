#!/bin/bash
set -e
pnpm install --frozen-lockfile
echo "Skipping automatic database push. Review lib/db/migrations/manual/ for production-safe migrations."
