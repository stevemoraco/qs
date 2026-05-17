#!/usr/bin/env bash
# Replit Run button entrypoint.
#
# Previously this script tore down all four artifact dev workflows and started a
# production bundle on the same ports for build verification. That behaviour
# made the Run button destructive: clicking it killed dev mode and squatted
# port 8080 with `node ./dist/index.mjs`, which then required manual cleanup
# before dev could resume.
#
# The four artifact workflows (api-server, web, mobile, mockup-sandbox) are
# managed by Replit's workflow system and auto-start with the workspace, so the
# Run button does not need to start anything. It just needs to be harmless.
#
set -euo pipefail

echo "Run button: dev mode is managed by the four artifact workflows."
echo "Use package scripts for non-destructive checks: pnpm run typecheck, pnpm run smoke, or individual builds."
exit 0
