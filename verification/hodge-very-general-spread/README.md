# Public verifier — Hodge very-general spread finite core

**Status:** finite logical replay only. **Not** a formalization of relative Chow spaces, Baire category, algebraic cycles, Hodge loci, or the Hodge Conjecture.

## Canonical private provenance

- Repository/branch: `stevemoraco/RH-Lean:agent/hodge-very-general-spread-20260812`
- Private note: `research/hodge/HODGE_VERY_GENERAL_ALGEBRAICITY_SPREAD_THEOREM_2026-08-12.md`
- Exact Lean blob: `85414a13c59aea18f6f41f2bc1e979db087c88a1`

## Replayed declarations

1. `every_fiber_has_witness_of_surjective_family`
2. `every_fiber_has_parameter_and_witness`
3. `one_uniform_type_closes_all_fibers`
4. `missing_base_point_blocks_witness_transfer`

## Scope firewall

The source checks only the final logical step after one surjective equality component has already been constructed. It does not formalize:

- countable Chow realization loci;
- properness or Baire category;
- flat cycle-class local systems;
- monodromy or Hodge loci;
- algebraic cycles or the Hodge Conjecture.

A green replay validates only the four declarations and their printed axiom reports.

Five-alarm status: OFF.
