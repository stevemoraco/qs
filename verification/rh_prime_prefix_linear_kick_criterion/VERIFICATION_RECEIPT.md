# RH prime-prefix linear-kick criterion finite core — verification receipt

Date: 2026-08-13 UTC

Status: **LEAN-VERIFIED ABSTRACT DIVERGENCE-TRANSFER CORE / NOT RH / SIX-ALARM OFF.**

## Canonical source

- path: `verification/rh_prime_prefix_linear_kick_criterion/RHPrimePrefixLinearKickCriterion.lean`
- Git blob: `77b38ff29794a0868eb28d001c2427c790c76461`
- SHA-256: `a3ad9124967782b7bb43f2e65837963cde0e6f7ac2e25397132ab03300448d23`
- branch: `agent/rh-prime-prefix-linear-kick-criterion-verifier-20260813`
- verifier source head: `3600d1a46fb146c87dab77bd8355dd80a8d7d3d0`

The source imports Mathlib and contains no `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`. The workflow byte-locks the source blob before compilation.

## Verified declarations

1. `remainder_sandwich`
2. `diverges_mono`
3. `diverges_of_bounded_upper_defect`
4. `diverges_iff_of_bounded_nonnegative_remainder`
5. `diverges_iff_add_bounded_shift`
6. `diverges_eventually_positive`
7. `equivalent_problem_transfer`
8. `finite_remainder_sandwich`

## Successful public hostile replay

- repository: `stevemoraco/qs`
- workflow run: `31678274685`
- job: `94377534390`
- runner: Ubuntu `22.04.5 LTS`
- compiler environment: AXLE Lean `4.30.0`
- source blob gate: passed
- trust-token preflight: passed
- `okay=true`
- failed declarations: `[]`
- Lean errors / warnings: `[] / []`
- AXLE tool errors / warnings: `[] / []`
- artifact: `9173155915`
- artifact digest: `sha256:a6b8f255f36f8d355897afc2a11832e85b3ad0cbc73adf41d474bd1a376dc515`

All eight printed theorem dependency sets are empty:

```text
[].
```

Thus this abstract logical core uses no reported axioms at all.

## Scope boundary

The file verifies only the finite/order-theoretic shell:

- bounded nonnegative remainders do not change divergence to `+infinity`;
- bounded deterministic shifts do not change divergence;
- divergence implies eventual positivity;
- an abstract equivalent problem transfers across such a decomposition.

It does not define primes, logarithms, Chebyshev functions, the Bregman root corridor, convergence of the actual remainder series, Johnston's theorem, zeta, or RH. Those are separate human analytic dependencies in `stevemoraco/RH`.
