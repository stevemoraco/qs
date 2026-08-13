# RH prime-prefix fixed-gauge Bregman finite core — verification receipt

Date: 2026-08-13 UTC

Status: **LEAN-VERIFIED FINITE REAL-ALGEBRA CORE / NOT RH / SIX-ALARM OFF.**

## Canonical source

- path: `verification/rh_prime_prefix_fixed_gauge_bregman/RHPrimePrefixFixedGaugeBregman.lean`
- Git blob: `aa5e52b1aa69d69c62c9bb0e20df258d1cf5a04f`
- SHA-256: `d1d22f942e96a26d0622ad461eedd20416dc24e9a584ea73a27e0f0d60efca65`
- branch: `agent/rh-prime-prefix-fixed-gauge-bregman-verifier-20260813`
- canonical verifier head: `1a20bfe51aa137eecefb6d6d9e3d3a58dfc95f2e`

The source imports Mathlib and contains no `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`. The workflow byte-locks the source blob before compilation.

## Verified declarations

1. `square_increment_linearization`
2. `square_increment_remainder`
3. `fixed_tangent_bregman_identity`
4. `reciprocal_remainder_positive`
5. `threshold_excess_linear_term`
6. `fixed_gauge_bregman_decomposition`
7. `fixed_gauge_tangent_domination`
8. `fixed_weight_closed_form`
9. `fixed_weight_positive`
10. `finite_fixed_gauge_ledger`
11. `finite_fixed_gauge_domination`

## Successful public hostile replay

- repository: `stevemoraco/qs`
- workflow run: `31677031800`
- job: `94373738419`
- runner: Ubuntu `22.04.5 LTS`
- compiler environment: AXLE Lean `4.30.0`
- source blob gate: passed
- trust-token preflight: passed
- `okay=true`
- failed declarations: `[]`
- Lean errors / warnings: `[] / []`
- AXLE tool errors / warnings: `[] / []`
- artifact: `9171926402`
- artifact digest: `sha256:400d3b5573f217dcdf1661e96fbd5668c9c873366f747535832d50c83ede6c1a`

Every printed dependency set is contained in

```text
{propext, Classical.choice, Quot.sound}.
```

No custom result-carrying axiom appears.

## Failed-first chronology

The failed attempts are preserved rather than overwritten:

- run `31676542771`, job `94372243703`: exposed one redundant tactic and an uncleared denominator in the closed-form weight theorem;
- run `31676692738`, job `94372703526`: the coefficient normalization remained incomplete;
- run `31676840507`, job `94373150474`: all eleven declarations compiled, but the workflow intentionally rejected proof-script lint warnings;
- run `31677031800`, job `94373738419`: warning-free success.

This chronology demonstrates that the compiler firewall changed the source and was not a ceremonial replay.

## Mathematical boundary

The file verifies finite scalar identities, positivity, and finite summation. It does **not** define primes, logarithms as prime data, Chebyshev functions, Johnston's analytic criterion, the Riemann zeta function, or the Riemann Hypothesis. The arithmetic weighted-kick lower bound needed to conclude RH remains unproved.
