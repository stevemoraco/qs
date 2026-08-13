# B2 round 41 provenance audit

Date: 2026-08-13 UTC

## Verdict

🔴 REFUTED — the previously reported pushed `stevemoraco/qs` head
`002b62de473707ae62d26cfa18074b757ec7a580` on branch
`automation/b2-adversarial-braid-20260813-round40` is not present in the
connected GitHub repository at audit time.

🧱 OBSTRUCTION — no mathematical conclusion may inherit authority from that
unreconstructible branch/commit report.

## Exact claim tested

The report asserted that repository `stevemoraco/qs` contained the branch
`automation/b2-adversarial-braid-20260813-round40` with final commit
`002b62de473707ae62d26cfa18074b757ec7a580`.

## Proof / certificate

1. GitHub's repository endpoint identifies `stevemoraco/qs`, with default
   branch `main`, and grants this connector read/write access.
2. Fetching
   `GET /repos/stevemoraco/qs/commits/002b62de473707ae62d26cfa18074b757ec7a580`
   returned `No commit found for SHA` with HTTP status 422.
3. Searching repository branches for `round40`, `automation/b2`, and `braid`
   returned no matching branch.
4. Paging the branch inventory exposed the actual current automation and agent
   refs but not the asserted ref.

This is enough to refute the operational claim that the named SHA is a current
pushed commit in this repository. It does not prove that no identically named
local branch, deleted ref, fork, or other repository ever existed.

## Corrected base used here

🟢 PROVED — the extant additive six-lane bank ref
`automation/b4-auto20-run7-live-edge-bank-20260813-0409z` resolves to exact
commit
`e9e4c2e2fa6bf8b66c29a2a8b4a8a93cb7a9f71a`.

GitHub comparison against `main` at
`a0443bf09b41a02a5b860bcfbf10e3e83fa5b370` reports this bank as 70 commits
ahead and 0 behind. The present isolated branch was created directly from that
exact SHA. No merge, rebase, force update, or edit to another branch was used.

## Assumptions

- The connected GitHub API returned the authoritative current state of
  `stevemoraco/qs` at audit time.
- A 40-hex SHA is interpreted as a Git commit object in that repository.

## Critic verdict

🟢 PROVED as a current-repository provenance obstruction.

The conclusion must not be overstated: deleted or unpushed history is not ruled
out. Therefore the strongest justified correction is “not currently
reconstructible from the claimed repository,” not “never existed anywhere.”

## Lean status

- 🔵 LEAN-SOURCE: not applicable; this is a Git provenance certificate.
- ✅ LEAN-VERIFIED: NO.

## Exact remaining gap

🚧 MISSING — any party wishing to restore the round-40 claims must provide a
reachable repository/ref or a commit bundle whose object hash is exactly the
asserted SHA, plus parent/tree verification. Until then, all round-40
mathematical claims are treated only as untrusted prose and must be rederived.

## Provenance

- Repository: `stevemoraco/qs`
- Audited absent SHA: `002b62de473707ae62d26cfa18074b757ec7a580`
- Audited absent branch: `automation/b2-adversarial-braid-20260813-round40`
- Corrected exact base: `e9e4c2e2fa6bf8b66c29a2a8b4a8a93cb7a9f71a`
- New isolated branch: `automation/b2-adversarial-braid-realstate-20260813-round41`
