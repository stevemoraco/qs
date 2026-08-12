# Public verifier — P-versus-NP distinguisher geometry finite core

**Status:** finite scalar replay only. **Not** a formalization of Boolean sensitivity, bounded-depth circuits, MCSP, P, NP, or their separation.

## Canonical private provenance

- Repository/branch: `stevemoraco/RH-Lean:agent/pnp-distinguisher-sensitivity-alternation-barrier-20260812`
- Private note: `millennium/p-vs-np/PNP_DISTINGUISHER_SENSITIVITY_ALTERNATION_BARRIER_2026-08-12.md`
- Exact Lean blob: `4df286150faa9c318d2e2ef4aa1281e96ab0fd9f`

## Replayed declarations

1. `sensitivity_upper_meets_expansion_floor`
2. `alternation_upper_meets_block_floor`
3. `monotone_family_path_contradiction`
4. `bounded_combination_requires_many_tests`
5. `interval_count_floor`
6. `bounded_depth_sensitivity_gate`
7. `exponent_budget_identity`

## Scope firewall

The source checks scalar consequences after the combinatorial or source-backed hypotheses are supplied. It does not formalize:

- Boolean cubes or random paths;
- average sensitivity or monotone-path alternation;
- Boppana's bounded-depth theorem;
- distinguishers, succinct verification, or parity oracles;
- uniform circuit classes, MCSP, `PH`, `P`, or `NP`.

A green replay validates only the seven declarations and their printed axiom reports.

Five-alarm status: OFF.
