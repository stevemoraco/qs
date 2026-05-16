# QuantumShield

QuantumShield is a TypeScript monorepo for a post-quantum encrypted chat platform. It includes a React/Vite web app, an Expo mobile app, an Express API server, shared OpenAPI/Zod clients, and a Drizzle/PostgreSQL data layer.

## Status

This project is early-stage software. Treat cryptographic and security-sensitive changes as high risk: keep them small, reviewed, and covered by tests or documented manual verification.

## Stack

- pnpm workspaces, Node.js 24, TypeScript 5.9
- Web: React, Vite, Tailwind CSS, shadcn/ui, Wouter
- Mobile: Expo, React Native, Expo Router
- API: Express 5, PostgreSQL, Drizzle ORM
- API contract: OpenAPI in `lib/api-spec/openapi.yaml`, generated Zod schemas and React Query hooks
- Crypto dependencies: `@noble/post-quantum`, Web Crypto AES-GCM, argon2id

## Repository Layout

- `artifacts/web` - React web client
- `artifacts/mobile` - Expo mobile client
- `artifacts/api-server` - Express API server
- `lib/api-spec` - OpenAPI source of truth and code generation config
- `lib/api-zod` - generated/shared API validation schemas
- `lib/api-client-react` - generated/shared React Query client
- `lib/db` - Drizzle schema and database config
- `scripts` - repository maintenance scripts

## Requirements

- Node.js 24
- pnpm 10.26.1
- PostgreSQL for the API server

## Setup

```sh
pnpm install
```

Create local environment files as needed. Do not commit real secrets. At minimum, the API server expects:

```sh
DATABASE_URL=postgres://...
SESSION_SECRET=replace-me
```

## Development

```sh
pnpm --filter @workspace/api-server run dev
pnpm --filter @workspace/web run dev
pnpm --filter @workspace/mobile run dev
```

## Quality Gates

Run these before opening a pull request:

```sh
pnpm run typecheck
pnpm run build
pnpm audit --audit-level moderate
```

Regenerate API clients after changing the OpenAPI contract:

```sh
pnpm --filter @workspace/api-spec run codegen
```

Push database schema changes in development only:

```sh
pnpm --filter @workspace/db run push
```

## Security

Security reports should follow [SECURITY.md](SECURITY.md). The repo is configured with CI typechecks/builds, dependency review, Dependabot updates, CodeQL analysis, and a scheduled pnpm audit workflow.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for issue, pull request, review, and release guidance.

## License

MIT. See [LICENSE](LICENSE).
