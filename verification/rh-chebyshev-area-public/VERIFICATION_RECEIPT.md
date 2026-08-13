# Verification receipt — Johnston Chebyshev-area review core

Date: 2026-08-13 UTC

Status: ✅ **33 exact finite, genuine-prime, zeta-reflection, and conditional-logical Lean declarations verified. Not an RH proof.**

## Canonical public hostile replay

Repository: `stevemoraco/qs`

Branch: `agent/rh-chebyshev-area-public-verifier-20260813-gpt56`

Verified source head:

```text
5ae97439789d8fe0840bc44986269868e7d8c5f4
```

Pull-request merge commit checked by the runner:

```text
0ebb026ff27894d02d126756a3fcbe1fb12d6224
```

Workflow:

```text
name: RH Chebyshev area public verifier
run: 31702490830
job: 94454785825
conclusion: SUCCESS
```

## Exact source identities

```text
ChebyshevAreaFinite.lean
Git blob: f92f1a7c9749173070b405870f4a2903211efeee
SHA-256: 574fd5b9d7705f4ff7ff217ab2adf8598dd5e215ba1ab8a0833608351102c22c

ChebyshevAreaPrimeFinite.lean
Git blob: 884f61b5f5a6d6d71764a6941800cfa8b94f3e04
SHA-256: 39d2e9216b134ff17933e4b8bdc8cefd30a2a68243c53061e94e9e2fad9c04d3

ChebyshevAreaLandauSkeleton.lean
Git blob: e0c50376a91c9074b17338318fa1348d2d929b4c
SHA-256: a88a4d4e0a43d65ee096d024587e6f8bc08346e0d4d35d686d177e0ab9077f3c
```

The workflow checked all three Git blobs before compilation.

## Pinned toolchain

```text
Ubuntu 24.04.4 LTS
Lean 4.32.1
Lean commit f054605aea4b840552cca2e725580bffd1e1b704
Lake 5.0.0-src+f054605
Mathlib v4.32.1
Mathlib commit 520045ab14e26149ee970e2e617ca04b09bde5d6
```

## Trust boundary

The workflow rejected explicit occurrences of:

```text
sorry
admit
sorryAx
custom axiom declarations
opaque
unsafe
native_decide
Lean.ofReduceBool
```

All 33 staged `#print axioms` reports were present. Every report was exactly a subset of

```text
{propext, Classical.choice, Quot.sound}
```

No `sorryAx` or custom conclusion-carrying axiom appeared in the compiler output.

## Verified declaration groups

### Generic finite area geometry — 9 declarations

```text
area_eq_center_add_square
area_at_center
centerValue_le_area
area_eq_centerValue_iff
center_minimizes_on_interval
left_endpoint_minimizes
right_endpoint_minimizes
interval_minimizer_trichotomy
area_nonneg_of_centerValue_nonneg
```

### Genuine finite-prime arithmetic — 9 declarations

The definitions use Mathlib's actual `Nat.Prime` predicate and `Real.log` weights.

```text
thetaNat_succ
primeMoment_succ
primeArea_succ
primeArea_endpoint_compatible
primeArea_eq_center_add_square
primeCenter_le_primeArea
unitIntervalMinimum_le_primeArea
positive_on_unitInterval_iff
discreteJohnstonCriterion_iff
```

### Zeta reflection and Johnston logical endpoint — 15 declarations

```text
nontrivialZero_ne_zero
GammaR_ne_zero_of_nontrivialZero
completedRiemannZeta_eq_zero_of_nontrivialZero
reflected_riemannZeta_zero
reflected_not_trivial
reflected_ne_one
reflectsNontrivialZeros
riemannHypothesis_of_bounds
leftHalfBound_of_reflection
rightHalfBound_of_eventualNonnegative
riemannHypothesis_of_eventualNonnegative
eventuallyNonnegative_of_positiveAfterTwo
riemannHypothesis_of_positiveAfterTwo
riemannHypothesis_iff_eventuallyNonnegative
riemannHypothesis_iff_positiveAfterTwo
```

Zero reflection is proved internally from Mathlib's completed-zeta functional equation, the Gamma-factor zero classification, and zeta nonvanishing for real part at least one. It is not a packaged assumption in the final source.

The endpoint targets Mathlib's actual `RiemannHypothesis` definition. The remaining analytic hypotheses are explicit fields of `LandauBridge`; they are theorem parameters, not hidden or custom axioms, and they are not proved by this replay.

## Evidence artifact

```text
artifact ID: 9181872824
artifact name: rh-chebyshev-area-public-evidence
artifact ZIP SHA-256:
903ff70ea24e3ee5d5cb901136a60d9a4248d7f9de800f058b4b204e71239f71
```

The artifact contains source hashes, toolchain versions, complete Lean output, and the generated 33-declaration axiom report.

## Published theorem and exact unverified interfaces

Johnston's 2023 theorem states that, for

```text
A(x) = integral from 2 to x of (t - theta(t)) dt,
```

RH is equivalent to `A(x) > 0` for every `x > 2`.

This replay does not verify:

1. the real-variable Chebyshev function and its integral;
2. the finite-sum/integral identification;
3. Johnston's analytic RH equivalence;
4. the Mellin/prime-zeta continuation fields of `LandauBridge`;
5. Landau's theorem for nonnegative Mellin tails;
6. the RH-to-sign analytic direction;
7. the unconditional strict sign.

The solution-bearing missing statement is exactly

```text
for every x > 2,
integral from 2 to x of (t - theta(t)) dt > 0.
```

Equivalently at the verified finite-prime layer:

```text
for every natural n >= 2,
unitIntervalMinimum n > 0.
```

By Johnston's theorem, proving either universal statement is already proving RH.

**SIX-ALARM OFF.**
