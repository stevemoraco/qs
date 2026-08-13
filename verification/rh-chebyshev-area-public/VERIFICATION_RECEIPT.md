# Verification receipt — RH Chebyshev area finite and logical cores

Date: 2026-08-13 UTC

Status: ✅ exact finite and conditional-logical Lean cores verified. **Not an RH proof.**

## Canonical public replay

Repository: `stevemoraco/qs`

Branch: `agent/rh-chebyshev-area-public-verifier-20260813-gpt56`

Verified head:

```text
39b85d326a04441ae783056a73be6b7d360cb223
```

Workflow:

```text
name: RH Chebyshev area public verifier
run: 31698670268
job: 94442227491
conclusion: SUCCESS
```

## Exact source identities

```text
ChebyshevAreaFinite.lean
Git blob: f92f1a7c9749173070b405870f4a2903211efeee
SHA-256: 574fd5b9d7705f4ff7ff217ab2adf8598dd5e215ba1ab8a0833608351102c22c

ChebyshevAreaLandauSkeleton.lean
Git blob: 4c178f672979d947b3313bb28497f309c1e3f238
SHA-256: 67c5ed975c34916e570dd64cadb44c5a12815b440ccbe582f5de1648a12903fb
```

The workflow checked these Git blobs before compilation.

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

All 14 staged `#print axioms` reports were present. Every report was exactly a subset of

```text
{propext, Classical.choice, Quot.sound}
```

No `sorryAx` or custom conclusion-carrying axiom appeared in the compiler output.

## Verified declarations

Finite geometry:

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

Conditional logical skeleton:

```text
riemannHypothesis_of_bounds
leftHalfBound_of_reflection
rightHalfBound_of_eventualNonnegative
riemannHypothesis_of_eventualNonnegative
riemannHypothesis_iff_eventuallyNonnegative
```

The final skeleton theorem targets Mathlib's actual `RiemannHypothesis` definition. Its analytic hypotheses are explicit fields of `LandauBridge`; they are not hidden axioms and they are not proved by this replay.

## Evidence artifact

```text
artifact ID: 9180387125
artifact name: rh-chebyshev-area-public-evidence
artifact ZIP SHA-256:
37c435d43f96d9ed67cb50908f4e70491d112f4fb120665b1495b6bbc3ebcdec
expires: 2026-11-11T12:08:39Z
```

The artifact contains source hashes, toolchain versions, complete Lean output, and the generated axiom report.

## Exact unverified interfaces

This receipt does not verify:

1. the genuine prime-indexed Chebyshev function;
2. the integral identity defining the infinite area;
3. Johnston's published analytic RH equivalence;
4. the first Riesz explicit formula;
5. prime-zeta Möbius inversion and normal convergence;
6. Landau's theorem for nonnegative Mellin tails;
7. zeta-zero reflection as an instantiated theorem in this file;
8. the unconditional sign inequality.

The solution-bearing missing statement remains

```text
for every x > 2,
integral from 2 to x of (t - theta(t)) dt > 0.
```

By Johnston's theorem, proving that statement is already proving RH.

**SIX-ALARM OFF.**
