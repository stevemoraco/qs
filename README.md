# QuantumShield

QuantumShield is a post-quantum encrypted chat platform available at [quantumshield.co](https://quantumshield.co). It runs as a browser app, an installable PWA, and an Expo mobile app against the same Express API, OpenAPI clients, and PostgreSQL/Drizzle data layer.

## Start Here

- Use the live app: [quantumshield.co](https://quantumshield.co)
- Read this README on GitHub: [github.com/stevemoraco/qs#quantumshield](https://github.com/stevemoraco/qs#quantumshield)
- Install and use the app: [Using QuantumShield](https://github.com/stevemoraco/qs#using-quantumshield)
- Review privacy protections: [Privacy Behavior](https://github.com/stevemoraco/qs#privacy-behavior)
- Review release notes: [CHANGELOG.md](CHANGELOG.md)
- Run the project locally: [Development](https://github.com/stevemoraco/qs#development)
- Report vulnerabilities privately: [SECURITY.md](https://github.com/stevemoraco/qs/blob/main/SECURITY.md)
- Contribute patches: [CONTRIBUTING.md](https://github.com/stevemoraco/qs/blob/main/CONTRIBUTING.md)

## Using QuantumShield

QuantumShield has three supported surfaces:

- `Web app`: Open [quantumshield.co](https://quantumshield.co) in a modern browser and sign in or request clearance.
- `PWA`: Install [quantumshield.co](https://quantumshield.co) from Chrome, Edge, Safari, or a mobile browser so it launches from your home screen or app launcher.
- `Expo mobile app`: Run the native Expo client from this monorepo for device testing and mobile privacy controls.

All clients talk to the same API and use the same account system. Messages are encrypted client-side before they are sent. The server stores ciphertext, room metadata, push subscriptions, and lead/account records, but not message plaintext.

## PWA Install

Chrome or Edge on desktop:

1. Open [quantumshield.co](https://quantumshield.co).
2. Use the install icon in the address bar, or open the browser menu and choose `Install app`.
3. Launch QuantumShield from the installed app window.
4. Allow notifications when prompted so encrypted push alerts can be registered.
5. Create an account; post-quantum identity keys are generated locally on that device.

Chrome on Android:

1. Open [quantumshield.co](https://quantumshield.co).
2. Open the browser menu and choose `Install app` or `Add to Home screen`.
3. Open QuantumShield from the home screen.
4. Allow notifications before account creation.

Safari on iPhone or iPad:

1. Open [quantumshield.co](https://quantumshield.co) in Safari.
2. Tap `Share`, then `Add to Home Screen`.
3. Open QuantumShield from the home screen.
4. Enable notifications if the browser and OS version support web push.

The web registration flow intentionally checks for installed-app mode and notification permission before creating an account. This is implemented in `artifacts/web/src/components/SignupGate.tsx`.

## Expo Mobile App

The Expo app lives in `artifacts/mobile` and uses Expo Router. It is useful for native-device testing of chat, auth, push-adjacent flows, screenshot controls, and app-background behavior.

Run it locally:

```sh
pnpm install
pnpm --filter @workspace/api-server run dev
pnpm --filter @workspace/mobile run dev
```

Then open the Expo development URL or QR code with Expo Go or a compatible development build. The mobile app expects the API server to be reachable through the Replit/Expo environment variables configured in `artifacts/mobile/package.json`.

Mobile behavior to know:

- Message plaintext is not shown by default. Press and hold `Encrypted - hold to reveal` to decrypt a message whose key exists on the device.
- Releasing the press hides plaintext again.
- Backgrounding the app clears any currently revealed plaintext.
- `expo-screen-capture` attempts to prevent screen capture for the chat screen where the platform supports it.
- If a screenshot event is reported, the app shows a warning banner.

## Privacy Behavior

QuantumShield adds UI-level privacy controls on top of encryption. These controls reduce accidental exposure; they do not replace OS hardening, device security, or careful operational practice.

Web chat behavior:

- The chat surface is non-selectable and blocks the context menu.
- A global privacy shield covers the app when the window loses focus, the document is hidden, printing starts, or the `PrintScreen` key is detected.
- Individual room contents blur when the tab/window is hidden or blurred.
- Any revealed message plaintext is cleared on blur, tab hide, pointer release, pointer cancel, pointer leave, or message-list scroll.
- Messages use `Encrypted - hold to reveal`; plaintext is held in transient React state only while the interaction is active.
- The web app attempts on-device camera scanning in chat using the selfie camera and local model pipeline. If the model or camera is unavailable, the UI reports that scanning is offline.

Expo mobile behavior:

- The chat screen uses `expo-screen-capture` to request screenshot/screen-recording prevention where supported.
- Screenshot listener events trigger a visible warning banner.
- App background transitions clear any currently revealed plaintext.
- Messages use the same hold-to-reveal pattern as the web client.

These features are implemented primarily in `artifacts/web/src/pages/ChatApp.tsx`, `artifacts/web/src/index.css`, and `artifacts/mobile/app/app.tsx`.

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
