# Contributing

Thanks for helping maintain QuantumShield. This project handles authentication, encryption, and private messages, so changes should favor clarity, reviewability, and conservative defaults.

## Development Workflow

1. Open an issue for non-trivial behavior, API, crypto, storage, or security changes.
2. Keep pull requests focused. Avoid mixing refactors with feature or security fixes.
3. Update generated clients with `pnpm --filter @workspace/api-spec run codegen` when `lib/api-spec/openapi.yaml` changes.
4. Add or update tests when changing shared behavior, API contracts, auth, crypto, storage, or message lifecycle code.
5. Run `pnpm run typecheck`, `pnpm run build`, and `pnpm audit --audit-level moderate` before requesting review.

## Pull Request Guidance

Every PR should include:

- What changed and why.
- How it was verified.
- Screenshots or recordings for user-facing UI changes.
- Security impact notes for auth, crypto, storage, dependency, permission, logging, or network changes.
- Migration or rollout notes for API/database changes.

Reviewers should block on:

- Secrets, credentials, private keys, or uploaded prompt assets committed to Git.
- Unreviewed crypto changes or custom cryptographic primitives.
- Missing validation on API boundaries.
- Sensitive data logged, persisted unnecessarily, or exposed to the client.
- Dependency additions without a clear need and maintenance/security posture.

## Coding Standards

- Prefer existing workspace patterns over new abstractions.
- Keep API contracts explicit in OpenAPI and regenerate clients.
- Keep private keys client-side only.
- Use structured validation for untrusted input.
- Avoid committing generated build output unless a package explicitly requires it.

## Dependency Policy

- Use pnpm only.
- Keep `minimumReleaseAge` enabled in `pnpm-workspace.yaml`.
- Prefer established, maintained packages with clear licenses.
- Explain new runtime dependencies in the PR description.

## Responsible Disclosure

Do not open public issues for vulnerabilities. Follow [SECURITY.md](SECURITY.md).
