# Repository Instructions

- When the user asks to commit and push, commit on the current branch unless they explicitly ask for a new branch, worktree, or pull request.
- Do not create local branches or worktrees for commit/push requests without explicit user approval.
- If a temporary branch is accidentally created, move the requested commit back to the original branch and delete the temporary branch before reporting completion.
- Runtime release/version labels should be generated from the release commit or server boot metadata in Mountain Time, not hardcoded in application UI. Use the format `vYYYY.MM.DD.hh.mmAM/PM.MDT` or `vYYYY.MM.DD.hh.mmAM/PM.MST`, for example `v2026.05.17.09.23AM.MDT`.
