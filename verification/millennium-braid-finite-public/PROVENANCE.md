# Millennium braid three-core public replay provenance

Date: 2026-08-13 UTC

Status: **FIRST HOSTED REPLAY PARTIAL: HODGE FINITE CORE VERIFIED; NS SOURCE
WARNING-CLEANUP AND FULL THREE-SOURCE REPLAY REQUESTED; NO MILLENNIUM CLAIM;
SIX-ALARM OFF.**

This isolated `stevemoraco/qs` verifier contains byte-identical copies of
three finite scalar sources from separate `stevemoraco/RH-Lean` draft stacks.
The workflow gates every copy by its exact Git blob before compiling it under
one pinned Lean/Mathlib project.

## Canonical sources

| lane | RH-Lean PR/head | exact Git blob | SHA-256 | `#print axioms` reports |
|---|---|---|---|---:|
| Hodge | #928, `31f5af6962198314c8d3afe5112ffdc4491d7495` | `331438dc006a3088749dfc9e52ad38681ead5b8a` | `035bc5f18659c53d3cc3822b92b12b5fecd1097400a8272e86bb7e6d2b5eeced` | 10 |
| Navier--Stokes | #976, `9a0b837a6455df07e22a6a89b011a9bc1cb0150e` | `039323b80f1cb8fe89dece3a7380bf81d1b6bf1b` | `86e0497e7ab2747a35908a047209f8f60985415b1808f82af2abe5d2ae838f74` | 15 |
| Yang--Mills | #983, `3d1c775385fff7f7bd3c3a2b3f1f699fad9fce14` | `0992240d7a6985d61cb02d0429656cd71462d1e5` | `ae96052ed09a33dc62bbad4951532a5a0f8844a93b798eaac97b0d8ca15cb216` | 7 |

The replay branch starts from qs `main` at
`e832133f25f4432ffba007f99359989d1bb16734`.

## Pinned environment

- Lean: `leanprover/lean4:v4.32.1`;
- Mathlib tag: `v4.32.1`;
- expected resolved Mathlib commit:
  `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- runner: `ubuntu-24.04`;
- one runner and one downloaded cache for all three sources.

This follows the successful Mathlib replay pattern in qs PR #197, run
`31667821868`, job `94346087657`.  The independent foundation-only pattern is
recorded in qs PR #231, run `31671649737`, job `94357332421`.  By contrast,
qs PR #154 run `31616290775`, job `94179805166`, is a genuine failed Lean
compile and carries no verification claim.

## First hosted replay receipt

qs PR #310 run `31696019359`, job `94433860997`, executed on Ubuntu 24.04.4
with Lean 4.32.1 and the exact pinned Mathlib commit.  Source identity and
trust scans passed.  The Hodge source compiled with warnings as errors, emitted
all 10 requested axiom reports using only `propext` and `Quot.sound`, and had
kernel-output SHA-256
`668beec66131039858fb1919eb164a08edbcc720326d19d5da869b593c7eb31c`.

The NS source elaborated every declaration and emitted all 15 foundation-only
reports, but 22 tactic-linter warnings were promoted to errors.  The canonical
source above removes only the unreachable or unnecessarily sequenced tactic
calls.  The inherited shell `errexit` also prevented the first job from
reaching YM; the workflow now disables it inside the aggregate replay loop so
every source always runs and every log is preserved.  First-run artifact
`9179378606` has archive digest
`4f270b4d2b635e61f3110b73d0a185df48bbabc3c8ef435789d1b582892b71ba`.

## Exact formal scope

- `HodgePrimitiveSuspensionFinite.lean` proves only a finite commutative-ring
  coefficient recurrence and telescoping identities.  It does not formalize
  varieties, cohomology, Hodge structures, Chow groups, or the Hodge
  conjecture.
- `NSNoncollinearOctagonFinite.lean` proves only the explicit finite scalar
  octagon ledger, target/difference components, and tangent-defect identities.
  It does not formalize Fourier analysis, Leray projection, Euler or
  Navier--Stokes solutions, regularity, or blowup.
- `YMPureElectricDefectFinite.lean` proves only scalar consequences of assumed
  defect floors and reverse-Poincare budgets.  It does not formalize compact
  groups, Haar measure, gauge invariance, ground-state transforms, continuum
  Yang--Mills, or a mass gap.

The workflow rejects proof holes, custom trust declarations, and hidden
computational escapes; requires all 32 requested axiom reports; whitelists
only `propext`, `Quot.sound`, and `Classical.choice`; and preserves the exact
sources, toolchain, manifest, logs, hashes, and audit summaries even on
failure.

Only the exact Hodge finite source is called Lean-verified from the first
receipt.  The NS and YM finite sources remain unverified until a clean hosted
job succeeds and its preserved evidence is inspected.
