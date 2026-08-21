# Millennium braid five-core public replay provenance

Date: 2026-08-13 UTC

Status: **FOUR FINITE CORES HAVE REPRODUCIBLE HOSTED RECEIPTS;
INVERSE-FREE HILBERT COMPLETED-SQUARE CORE ADDED FOR A FIRST REPLAY;
NO MILLENNIUM CLAIM; SIX-ALARM OFF.**

This isolated `stevemoraco/qs` verifier contains byte-identical copies of
five finite sources drawn from the braid research stacks.
The workflow gates every copy by its exact Git blob before compiling it under
one pinned Lean/Mathlib project.

## Canonical sources

| lane | RH-Lean PR/head | exact Git blob | SHA-256 | `#print axioms` reports |
|---|---|---|---|---:|
| Hodge | #928, `31f5af6962198314c8d3afe5112ffdc4491d7495` | `331438dc006a3088749dfc9e52ad38681ead5b8a` | `035bc5f18659c53d3cc3822b92b12b5fecd1097400a8272e86bb7e6d2b5eeced` | 10 |
| Navier--Stokes | #976, `9a0b837a6455df07e22a6a89b011a9bc1cb0150e` | `039323b80f1cb8fe89dece3a7380bf81d1b6bf1b` | `86e0497e7ab2747a35908a047209f8f60985415b1808f82af2abe5d2ae838f74` | 15 |
| Yang--Mills | #983, `46455556507ee0878388c51ad6f048c3f6966674` | `030b4c18fc859434c220caaa3ed01519d229a9fe` | `94ef451cd7ad8fc406892285593feb97943ad619c92b91d23f3d7eb5f2f6b818` | 7 |
| RH | #992, `5293b4f170a84db5aa7ff3a41167c3308842743e` | `162ff3a480da4a58717eb2fd84da9be0f5a4a213` | `035f470022330ec1af80e3b4cb1170f4fa6aea49beb824d4bb5e6f7da2456901` | 4 |
| RH Hilbert upgrade | qs #310 candidate | `6452df9ad04056917ddf199afd4eb49b5a08d6f0` | `886e495e616bd65c6deefc1ab8ebedf14ef46e3b5d77f0018fb56936832361d5` | 4 |

The replay branch starts from qs `main` at
`e832133f25f4432ffba007f99359989d1bb16734`.

## Pinned environment

- Lean: `leanprover/lean4:v4.32.1`;
- Mathlib tag: `v4.32.1`;
- expected resolved Mathlib commit:
  `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- runner: `ubuntu-24.04`;
- one runner and one downloaded cache for all five sources.

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

qs PR #310 run `31698671976`, job `94442233779`, replayed the warning-clean
NS source.  It compiled with warnings as errors, emitted all 15 requested
reports with only `propext`, `Quot.sound`, and `Classical.choice`, and had
kernel-output SHA-256
`45fd1bfe133030ce199541b446e44b0fbad8f9573e30c2e0d87a1eb28c6befb6`.
The Hodge receipt reproduced byte-for-byte.  YM then exposed three ordinary
Lean 4.32 source failures: a missing `noncomputable` marker for `Real.exp` and
two obsolete order-lemma applications.  The canonical YM source above repairs
only those three lines.  Second-run artifact `9180396662` has archive digest
`bd7660970bc57827fa91e38735b522ed5de1889222d96f6a396b2300912b9665`.

## Four-core successful receipt

qs PR #310 run/job `31706185967/94467220976` compiled all four canonical
sources with warnings as errors.  All 36 axiom reports used only `propext`,
`Quot.sound`, and `Classical.choice`; no `sorryAx` occurred.  Artifact
`9183336029` has archive SHA-256
`b164f23d03d3553ff9a32f7577e64415d080104aeb7887e83fc7e570193a77f3`.
The durable receipt commit `56ecb991664d0367240557cc81c3841d862de786`
reproduced cleanly in run/job `31707539664/94471787302`.

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
- `RHOddWeilSchurResidualSquaredCore.lean` proves only a real-scalar Schur
  residual identity, its residual-budget inequality, and a scalar cofinal
  limit implication.  It does not formalize Hilbert-space operators, the Weil
  form, Yoshida coercivity, zeta, or RH.
- `RHHilbertCompletedSquare.lean` proves the exact residual-visible identity
  `Q(y)-Q(z)=<D(y-z),y-z>+2<Dz-b,y-z>` for a symmetric continuous
  real-linear operator, its exact-solution specialization, and the induced
  minimization under nonnegativity.  It assumes neither completeness nor
  coercivity.  It does not construct `D` or `z`, prove range/closed-range or
  residual stability, define the Weil form, or imply RH.
  It additionally proves the exact coercive penalty
  `Q(y)-Q(z)>=-||Dz-b||^2/mu` from an explicit `mu>0` form lower bound; it
  does not supply that lower bound for any Weil operator.

The workflow rejects proof holes, custom trust declarations, and hidden
computational escapes; requires all 40 requested axiom reports; whitelists
only `propext`, `Quot.sound`, and `Classical.choice`; and preserves the exact
sources, toolchain, manifest, logs, hashes, and audit summaries even on
failure.

The exact first four finite sources have clean reproducible hosted receipts.
The Hilbert upgrade remains source-only until a clean hosted job succeeds and
its preserved evidence is inspected.
