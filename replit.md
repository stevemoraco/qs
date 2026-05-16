# QuantumShield

Post-quantum encrypted chat platform using NIST FIPS 203/204 algorithms (ML-KEM-1024 + ML-DSA-87), with on-device camera surveillance detection and cryptographic message expiry.

## Run & Operate

- Workflows start automatically: `API Server`, `web`, `expo`
- `pnpm --filter @workspace/api-server run dev` — run the API server manually
- `pnpm run typecheck` — full typecheck across all packages
- `pnpm --filter @workspace/api-spec run codegen` — regenerate API hooks and Zod schemas from the OpenAPI spec
- `pnpm --filter @workspace/db run push` — push DB schema changes (dev only)
- Required env: `DATABASE_URL`, `SESSION_SECRET`

## Stack

- pnpm workspaces, Node.js 24, TypeScript 5.9
- API: Express 5 + PostgreSQL + Drizzle ORM
- Validation: Zod (zod/v4), drizzle-zod
- API codegen: Orval (from OpenAPI spec at `lib/api-spec/openapi.yaml`)
- Web: React + Vite + TailwindCSS + shadcn/ui + Wouter routing
- Mobile: Expo (React Native) + Expo Router
- PQ Crypto: `@noble/post-quantum` (ML-KEM-1024, ML-DSA-87 — import from submodules: `@noble/post-quantum/ml-kem.js`, `@noble/post-quantum/ml-dsa.js`)
- Symmetric: Web Crypto API AES-256-GCM
- Password hashing: argon2id
- Auth: Bearer token (stored in localStorage on web, AsyncStorage on mobile)

## Where things live

- `lib/api-spec/openapi.yaml` — OpenAPI contract (source of truth)
- `lib/api-zod/src/generated/` — generated Zod schemas
- `lib/api-client-react/src/generated/` — generated React Query hooks
- `lib/db/src/schema/` — Drizzle ORM schema (users, sessions, rooms, room_members, messages, pre_keys)
- `artifacts/api-server/src/routes/` — Express route handlers
- `artifacts/web/src/pages/` — Landing, Login, Register, ChatApp
- `artifacts/web/src/lib/` — auth.ts (token/key storage), crypto.ts (AES-256-GCM helpers)
- `artifacts/mobile/app/` — Expo screens (index, login, register, app)
- `artifacts/mobile/context/AuthContext.tsx` — auth state + AsyncStorage + setAuthTokenGetter

## Architecture decisions

- **Client-side key generation only**: ML-KEM-1024 and ML-DSA-87 key pairs are generated in the browser/device. Private keys never touch the server.
- **Triple-layer encryption**: AES-256-GCM symmetric encryption per message + ML-KEM key encapsulation per recipient + ML-DSA-87 signature per message.
- **Cryptographic message expiry**: When a message TTL expires, the AES-256-GCM key is destroyed client-side. The server retains only unreadable ciphertext.
- **Camera surveillance detection**: TensorFlow.js COCO-SSD model runs on-device, blanks the screen if a recording device is detected in the selfie camera view.
- **Bearer token auth**: Session tokens stored locally (not cookies) to support both PWA and native mobile clients against the same API.

## Product

- Sales landing page (`/`) explaining PQ encryption with live matrix rain effect and algorithm status panel
- Web chat PWA (`/app`) with E2E encrypted channels, message expiry countdown, camera threat detection
- Expo mobile app with full chat + auth flows, dark quantum theme
- Post-quantum registration: generates ML-KEM-1024 + ML-DSA-87 key pairs on-device, uploads public keys + signatures

## User preferences

_Populate as you build — explicit user instructions worth remembering across sessions._

## Gotchas

- `@noble/post-quantum` root import throws — always import from submodules: `@noble/post-quantum/ml-kem.js` and `@noble/post-quantum/ml-dsa.js`
- CSS `@import url(...)` for Google Fonts must come BEFORE `@import "tailwindcss"` (PostCSS requirement)
- `argon2` requires approved builds: run `pnpm approve-builds` if adding new environments
- Mobile workflow must be restarted (not just HMR) when adding new packages
- TensorFlow.js (`@tensorflow/tfjs` + `@tensorflow-models/coco-ssd`) is dynamically imported in ChatApp to avoid blocking initial load

## Pointers

- See the `pnpm-workspace` skill for workspace structure, TypeScript setup, and package details
