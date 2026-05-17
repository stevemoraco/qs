#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

API_PORT="${API_PORT:-8080}"
WEB_PORT="${WEB_PORT:-5173}"
API_URL="http://127.0.0.1:${API_PORT}"
WEB_URL="http://127.0.0.1:${WEB_PORT}"
HEAD_SHORT="$(git rev-parse --short HEAD)"

kill_matching() {
  local pattern="$1"
  local pids
  pids="$(pgrep -f "$pattern" || true)"
  if [[ -n "$pids" ]]; then
    # shellcheck disable=SC2086
    kill $pids 2>/dev/null || true
  fi
}

wait_for_url() {
  local url="$1"
  local name="$2"
  local attempts="${3:-60}"
  for _ in $(seq 1 "$attempts"); do
    if curl -fsS "$url" >/dev/null 2>&1; then
      return 0
    fi
    sleep 0.5
  done
  echo "Timed out waiting for ${name} at ${url}" >&2
  return 1
}

echo "Stopping stale API/PWA preview processes..."
kill_matching "pnpm --filter @workspace/api-server run start"
kill_matching "node --enable-source-maps ./dist/index.mjs"
kill_matching "pnpm --filter @workspace/web run dev"
kill_matching "pnpm --filter @workspace/web run serve"
kill_matching "vite --config vite.config.ts"
sleep 1

echo "Building API and PWA for ${HEAD_SHORT}..."
pnpm --filter @workspace/api-client-react exec tsc -p tsconfig.json
pnpm --filter @workspace/api-server run build
pnpm --filter @workspace/web run build

if ! rg -q "$HEAD_SHORT" artifacts/web/dist/public/assets; then
  echo "Built PWA assets do not contain current commit ${HEAD_SHORT}." >&2
  exit 1
fi

echo "Starting API on ${API_URL}..."
PORT="$API_PORT" pnpm --filter @workspace/api-server run start &
API_PID=$!

wait_for_url "${API_URL}/api/healthz" "API"

echo "Starting built PWA preview on ${WEB_URL}..."
PORT="$WEB_PORT" API_PROXY_TARGET="$API_URL" pnpm --filter @workspace/web run serve &
WEB_PID=$!

wait_for_url "${WEB_URL}" "PWA"
wait_for_url "${WEB_URL}/api/version" "PWA API proxy"

INDEX_JS="$(curl -fsS "${WEB_URL}" | rg -m 1 -o '/assets/index-[^"]+\\.js')"
if [[ -z "$INDEX_JS" ]]; then
  echo "Could not find built index asset in served PWA HTML." >&2
  exit 1
fi
INDEX_SOURCE="$(curl -fsS "${WEB_URL}${INDEX_JS}")"
if ! rg -q "$HEAD_SHORT" <<<"$INDEX_SOURCE"; then
  echo "Served PWA asset ${INDEX_JS} does not contain current commit ${HEAD_SHORT}." >&2
  exit 1
fi

VERSION_JSON="$(curl -fsS "${API_URL}/api/version")"
if ! node -e '
const version = JSON.parse(process.argv[1]);
if (!version.latestCodeRunning) {
  console.error("API latestCodeRunning=false");
  process.exit(1);
}
if (version.git?.boot?.shortCommit !== process.argv[2]) {
  console.error(`API boot commit ${version.git?.boot?.shortCommit} !== ${process.argv[2]}`);
  process.exit(1);
}
' "$VERSION_JSON" "$HEAD_SHORT"; then
  exit 1
fi

echo "Latest PWA is serving ${HEAD_SHORT}."
echo "API pid: ${API_PID}"
echo "PWA pid: ${WEB_PID}"
wait
