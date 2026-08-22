# Public verifier — pedigree-polytope P=NP audit finite core

**Status:** finite logical/type replay only. **Not** a formalization of pedigree polytopes, multicommodity flow, Tardos's algorithm, complexity classes, or `P=NP`.

## Canonical private provenance

- Repository/branch: `stevemoraco/RH-Lean:agent/pnp-pedigree-lean-fatal-audit-20260812`
- Audit: `research/p_vs_np/PNP_PEDIGREE_POLYTOPE_LEAN_FATAL_AUDIT_2026-08-12.md`
- Exact canonical Lean blob: `b3cebf17d0104286f46ad1f258960c05f469be2d`

## Replayed declarations

1. `sufficiency_only`
2. `sufficiency_not_a_decider`
3. `no_membership_equivalence`
4. `opaque_target_transfer`
5. `unit_type_erases_points`

## Scope firewall

A green replay establishes only the elementary facts that a one-sided sound test can have false negatives, an official target needs a semantic equivalence to a repository-local proposition, and `Unit` erases point distinctions.

It does not audit the external source inside Lean, formalize its custom axioms, or settle `P` versus `NP`.

Five-alarm status: OFF.
