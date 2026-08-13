# Millennium braid three-core public replay provenance

Date: 2026-08-13 UTC

Status: **PUBLIC REPLAY REQUESTED; NO SUCCESSFUL COMPILER OR AXIOM RECEIPT YET;
NO MILLENNIUM CLAIM; SIX-ALARM OFF.**

This isolated `stevemoraco/qs` verifier contains byte-identical copies of
three finite scalar sources from separate `stevemoraco/RH-Lean` draft stacks.
The workflow gates every copy by its exact Git blob before compiling it under
one pinned Lean/Mathlib project.

## Canonical sources

| lane | RH-Lean PR/head | exact Git blob | SHA-256 | `#print axioms` reports |
|---|---|---|---|---:|
| Hodge | #928, `31f5af6962198314c8d3afe5112ffdc4491d7495` | `331438dc006a3088749dfc9e52ad38681ead5b8a` | `035bc5f18659c53d3cc3822b92b12b5fecd1097400a8272e86bb7e6d2b5eeced` | 10 |
| Navier--Stokes | #976, `8948bc04eced422869184d56c58b8bdc3cbc4a14` | `1aaeb8d4eebc299bd1c7ab003b12c46aecb7d4b0` | `de0585204a9acb3bbcaf133c813c97efc58b86d828333e5fc9296b21f698d286` | 15 |
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

No source is called Lean-verified until the hosted job succeeds and its
preserved artifact is inspected.
