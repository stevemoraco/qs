# Corrected RH-Lean round-40 provenance

Date: 2026-08-13 UTC

## Status

🟢 PROVED repository-state certificate.

🔵 LEAN-SOURCE exists.

✅ LEAN-VERIFIED: NO.

## Exact findings

The prior round-40 report mixed one false publication claim with one true
source-state claim.

### `stevemoraco/qs`

🔴 REFUTED — the reported qs branch
`automation/b2-adversarial-braid-20260813-round40` and commit
`002b62de473707ae62d26cfa18074b757ec7a580` are not present in the connected
repository.  See `00-provenance-audit.md`.

### `stevemoraco/RH-Lean`

🟢 PROVED — the branch
`automation/b2-round40-renewal-defect-cores-20260813` currently resolves to
exact commit

`495580ef37f34ff55fc854cb41644e684fccd5bd`.

🟢 PROVED — draft pull request `stevemoraco/RH-Lean#806` is open with that exact
head.  Its own body correctly labels the artifact source-only.

🧱 OBSTRUCTION — querying GitHub Actions for that exact head SHA returns zero
workflow runs.  Therefore no compiler replay, kernel acceptance, or axiom-log
certificate is attached to the head through GitHub Actions.

## Critic verdict

The strongest justified status is:

- branch/commit/PR provenance: 🟢 PROVED;
- Lean text present: 🔵 LEAN-SOURCE;
- theorem compiled by a clean Lean kernel: 🚧 MISSING;
- ✅ LEAN-VERIFIED: NO.

The absence of an Actions run does not prove that nobody compiled the file on a
private machine.  It does prove that the previously demanded public replay
certificate is absent from the claimed GitHub head.

## Assumptions

- GitHub's current repository, pull-request, and Actions endpoints are the
authoritative public/connected state at audit time.
- “LEAN-VERIFIED” requires an inspectable clean replay rather than source text
  and `#print axioms` commands alone.

## Exact remaining gap

🚧 MISSING — run the pinned project in a clean environment, preserve full
compiler output, inspect all `#print axioms` results, reject `sorryAx` and custom
proof carriers, and bind the evidence to the exact source SHA.

## Provenance

- Repository: `stevemoraco/RH-Lean`
- Branch: `automation/b2-round40-renewal-defect-cores-20260813`
- Head: `495580ef37f34ff55fc854cb41644e684fccd5bd`
- Draft PR: `#806`
- Actions query at audit time: zero runs for the exact head SHA.
