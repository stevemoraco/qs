# Security Policy

## Supported Versions

This project is pre-1.0. Security fixes are made on the default branch unless maintainers publish a supported release line.

## Reporting a Vulnerability

Please do not report vulnerabilities in public issues or pull requests.

Use GitHub private vulnerability reporting when available. If it is not enabled, contact the maintainers through the repository owner profile and include:

- Affected component or package.
- Reproduction steps or proof of concept.
- Expected and actual impact.
- Whether credentials, private keys, tokens, or user data may be exposed.
- Suggested fix, if known.

Maintainers should acknowledge reports within 7 days and provide a remediation plan or status update within 30 days.

## Security Review Scope

Security-sensitive areas include:

- Authentication, sessions, tokens, and authorization checks.
- Client-side key generation, key storage, encryption, signing, and message expiry.
- API validation and OpenAPI contract changes.
- Database schema, migrations, and row access assumptions.
- Push notifications and WebSocket message handling.
- Camera/sensor permissions and privacy-sensitive mobile APIs.
- Logging, telemetry, analytics, and error reporting.
- Dependency, build, and release pipeline changes.

## Audit Baseline

The repository should keep these controls active:

- pnpm lockfile committed and package manager pinned.
- pnpm `minimumReleaseAge` enabled for supply-chain delay.
- CI running typecheck and build on pull requests.
- Dependency Review on pull requests.
- CodeQL analysis on pushes and pull requests.
- Scheduled `pnpm audit --audit-level moderate`.
- Dependabot alerts and grouped npm/GitHub Actions updates.

## Secret Handling

- Never commit `.env`, private keys, session secrets, database URLs, VAPID keys, tokens, uploaded prompt assets, or local Replit/Codex state.
- Rotate any secret that is committed, pasted into an issue, or exposed in logs.
- Keep production secrets in the deployment platform secret store.
