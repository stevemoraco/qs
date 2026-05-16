# Changelog

## v2026.05.16.1108MDT

Released: 2026-05-16

This release prepares QuantumShield for open-source maintainers and auditors. It documents the current product surface, tightens the PWA and Expo privacy behavior, adds shareable metadata and open-source entry points, and syncs the web/mobile clients around the same hold-to-reveal privacy model.

### Maintainer Summary

- Published a clear project README for web, PWA, Expo, API, database, generated API clients, setup, development, quality gates, security reporting, and contribution flow.
- Added open-source repository hygiene: license, contribution guide, security policy, code of conduct, issue templates, pull request template, Dependabot config, and CI/security workflow setup.
- Added lead capture and SEO metadata for public launch readiness, including robots and sitemap files.
- Added public GitHub and audit entry points to the landing, login, and mobile auth surfaces.
- Improved PWA metadata and app sharing so installed/shared links have better title, description, icon, favicon, and Open Graph presentation.
- Preserved Replit deployment compatibility while avoiding workflow-file updates in commits pushed with the current token scope.

### Web And PWA Privacy

- Moved the foreground camera scanner from room-only mounting to the chat app shell, so the PWA requests and maintains the front-facing camera stream while the foreground chat app is open.
- Kept on-device vision inference local to the browser using the existing cached model pipeline and service worker cache support.
- Added camera status reporting for scanner initialization, clear state, detected recording-device threats, unavailable camera, denied permission, model unavailable, and scan errors.
- Added a global privacy shield that covers the app when focus is lost, the document is hidden, printing starts, or the `PrintScreen` key is detected.
- Kept secure chat content non-selectable and context-menu blocked to reduce accidental disclosure.
- Kept message plaintext encrypted at rest and rendered only during active hold-to-reveal interactions.
- Cleared revealed message plaintext on pointer release, pointer cancel, pointer leave, blur, tab hide, and message-list scroll.
- Replaced visually exposed account, room, search-result, and sender names with shuffled per-session device codenames.
- Revealed real contact/channel/sender names only while the user actively holds the relevant UI element or message reveal.
- Fixed mobile PWA back-swipe behavior by redirecting authenticated `/login` visits back to `/app` with history replacement.
- Changed successful login navigation to replace the login history entry so authenticated users do not get sent back to the login page by browser gestures.

### Expo Mobile Privacy

- Added `expo-camera` at the Expo SDK 54-compatible version.
- Mounted a persistent front-facing camera sentinel while the app is foregrounded and permission is granted.
- Added camera status reporting for front camera permission, startup, live state, denial, and mount errors.
- Kept OS-aware behavior: the app cannot keep camera access active while the OS backgrounds or suspends it.
- Preserved `expo-screen-capture` protection for chat screens where supported by the platform.
- Kept screenshot listener warnings for platforms that report screenshot events.
- Cleared revealed plaintext when the app leaves the active foreground state.
- Replaced room, account, search-result, and sender labels with shuffled per-session codenames by default.
- Revealed real names only during active hold interactions.
- Kept message plaintext reveal tied to press-and-hold interactions and cleared on release.

### Messaging And Crypto Behavior

- Kept message encryption client-side before send.
- Stored message keys only on the originating device so sent messages can be revealed locally without server plaintext.
- Removed plaintext retention after send success.
- Kept encrypted message bubbles as the default rendered state.
- Limited transient plaintext to active UI reveal state for messages whose keys exist on the device.
- Documented that server-side storage is ciphertext plus metadata, not message plaintext.

### Public Site And Sharing

- Added landing page sections for project ethos, open-source auditability, community participation, and security posture.
- Added GitHub links to public web and mobile auth surfaces.
- Added README sections for using the web app, installing the PWA, running the Expo app, privacy behavior, stack, layout, setup, development, quality gates, security, contributing, and license.
- Added SEO and lead-capture support for public launch readiness.
- Updated PWA/share metadata so the app is easier to recognize when installed or shared.

### Remote Sync

- Synced `main` to `origin/main` through the latest privacy and PWA navigation fixes before this release note.
- This release note should be committed and pushed as the maintainer-facing marker for `v2026.05.16`.

### Verification Run Today

- `pnpm --filter @workspace/web run typecheck`
- `pnpm --filter @workspace/mobile run typecheck`
- `pnpm --filter @workspace/web run build`

### Known Platform Limits

- Browser and mobile operating systems may suspend camera access when the app is backgrounded, unfocused, permission-denied, or otherwise restricted by platform policy.
- Web screenshot prevention is best-effort. The app can react to focus, print, visibility, and keyboard signals, but browsers do not provide complete screenshot blocking.
- Native screenshot prevention depends on platform support exposed through `expo-screen-capture`.
- On-device inference availability depends on browser support, cached assets, model load success, and available runtime backends.
