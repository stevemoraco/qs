# Repository Instructions

- When the user asks to commit and push, commit on the current branch unless they explicitly ask for a new branch, worktree, or pull request.
- Do not create local branches or worktrees for commit/push requests without explicit user approval.
- If a temporary branch is accidentally created, move the requested commit back to the original branch and delete the temporary branch before reporting completion.
- Runtime release/version labels should be generated from the release commit or server boot metadata in Mountain Time, not hardcoded in application UI. Use the format `vYYYY.MM.DD.hh.mmAM/PM.MDT` or `vYYYY.MM.DD.hh.mmAM/PM.MST`, for example `v2026.05.17.09.23AM.MDT`.
- When the user asks whether Replit is serving the latest PWA, run `pnpm run replit:latest` from the repo root. That script kills stale API/PWA Vite processes, rebuilds the API and PWA from the current `HEAD`, serves the built PWA preview on port `5173`, proxies `/api` to port `8080`, verifies `/api/version` reports the current boot commit, and verifies the served built JS asset contains the current short git SHA.
- Do not rely on a previously built `artifacts/web/dist/public` bundle after committing. The web version badge embeds `__QS_CLIENT_COMMIT__` at Vite build time, so any commit after `pnpm --filter @workspace/web run build` requires another build before serving the PWA.
- The Replit Run button should use the `Project` workflow, which runs `pnpm run replit:latest`. If another agent changes workflow configuration, restore this invariant before claiming the preview is current.
