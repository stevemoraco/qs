# Public verifier — RH deletion/insertion Schur finite core

**Status:** finite scalar/logical replay only. **Not** a formalization of Riesz sequences, infinite Gram operators, zeta zeros, or RH.

## Canonical private provenance

- Repository/branch: `stevemoraco/RH-Lean:agent/rh-confluent-grid-block-symbol-20260812`
- Private note: `scratch/rh_braid/RH_DELETION_HARMLESS_INSERTION_SCHUR_GATE_2026-08-12.md`
- Exact Lean blob: `2ba12cc6c67f78d4987287a27dacb58448936933`

## Replayed declarations

1. `lower_bound_restricts_through_isometric_extension`
2. `insertion_quadratic_positive`
3. `inserted_pivot_positive`
4. `duplicate_zero_mode`
5. `duplicate_gram_determinant_zero`
6. `positive_schur_determinant_iff`

## Scope firewall

The source checks only:

- abstract extension-by-zero lower-bound transfer;
- positivity of a scalar two-sector quadratic form under a positive determinant;
- the duplicate zero mode.

It does not formalize Hilbert-space synthesis operators, principal Gram compressions, operator square roots, Schur complements, zeta nodes, or RH.

A green replay validates only the six declarations and their printed axiom reports.

Five-alarm status: OFF.
