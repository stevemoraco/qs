# Hodge local Atiyah-residue firewall — receipt

**Date:** 2026-08-13  
**Status:** 🟢 PROVED (finite algebra) · 🔵 LEAN-SOURCE · ✅ LEAN-VERIFIED · 🧱 OBSTRUCTION · 🚧 HODGE BRIDGE MISSING  
**Six-alarm:** OFF

## Exact source

- Path: `verification/hodge_local_atiyah_residue/HodgeLocalAtiyahResidue.lean`
- Corrected source commit: `f6790a6f208f5520fc369e4ce47e014aac8422fe`
- Git blob: `82fccae997541a8ad927d09bf83ee8242b2dfc92`
- SHA-256: `25add44f824f1f1da4470f84a8ee7ad0cb2ea677ec3cd4ea9bf01ebf7c401c58`

## BANKER → CRITIC → CLEANER

`banker_residue_annihilates_degreeTwo_boundary` assumes rings `R,K`, a homomorphism `ε : R →+* K`, elements `u,v,w,z` with `ε u = ε v = ε w = ε z = 0`, and arbitrary degree-one homotopy data. It proves both residue components of the concrete row `D₁h⁻¹+h⁰D₀` vanish, for

```text
D₀ = [[-v,0],[u,0],[0,-z],[0,w]],  D₁ = [-u,-v,w,z].
```

`critic_nonminimal_differential_can_hit_unit_row` gives an explicit integer witness with `u=1`, `v=w=z=0`, for which the boundary equals `(1,0)`. Minimality/residue-vanishing is therefore necessary.

`cleaner_nonzero_residue_cocycle_not_boundary` proves that, under the BANKER assumptions, any row whose first or second residue component is nonzero is not a degree-two boundary. The intended geometric instance is `(1,0)` modulo `(u,v,w,z)`.

## Provenance

Extracted from `stevemoraco/qs#312`, file `research_bank/HODGE_W2_PARTIAL_NORMALIZATION_EXACT_SECANT_AND_LOCAL_SEMIREG_OBSTRUCTION_2026-08-13.md`. That note computes the local three-term complex over `ℂ[[u,v,w,z]]` and a contracted Atiyah-square row `(1,0)`. This Lean file formalizes only the final finite boundary/residue implication.

## Failed-first record

Initial commit/blob: `af0fec5c445da4b1ea60533e439c99d65743671b` / `f66e4e76fbdc4ab9ac65690573a9ffc63365b275`. PR #314 run/job `31698102893 / 94440431351` compiled with `okay=true` and no errors, but the warning-strict verdict failed because `[Nontrivial K]` was unused. Artifact `9180115759`, digest `sha256:dd4118e717bd0139947a6f6883778b5fd1cd89ab84b13e9afa2da8c9b4c1e4a2`. The repair removed the unnecessary assumption; no conclusion changed.

## Successful replay

PR #315, verifier head `67c8e14accd276b143d15e0bd4b22f855c2c43d7`, checked merge commit `1dc97c18e6c2b4d706b1a0ecb2165d841f0906e0`, run/job `31698230448 / 94440842514`, runner `GitHub Actions 1000021028`, AXLE `lean-4.30.0`, uncached request `4bd76e90-390b-4f40-bd22-33ed87cb8dd6`.

Result: `okay=true`; failed declarations, Lean errors/warnings, tool errors/warnings, and request failures were all empty. Evidence artifact `9180163941`, digest `sha256:0c55c64c46a4a46d6eb69930799639b0f282e5c7012240b403c79c9da1b0f2aa`.

Printed dependencies:

```text
BANKER  [propext, Quot.sound]
CRITIC  [propext, Classical.choice, Quot.sound]
CLEANER [propext, Quot.sound]
```

Static preflight found exactly three theorem declarations and three `#print axioms` commands, with no `sorry`, `admit`, `sorryAx`, user declaration of `axiom`, `opaque`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`.

## Exact remaining gap

Not formalized: the power-series local ring; exactness/minimality of the free complex; the mapping cone; the Atiyah/HKR computation; identification with local `Ext²`; localization to the global characteristic evaluation; the semiregularity square; construction of a replacement pure Cohen–Macaulay surface; deformation to cycles; or the official Hodge conjecture.

If the geometric inputs survive formalization, this result blocks the transverse-node partial-normalization architecture. The rebuilt target is a nonnormal, reducible, or nonreduced pure codimension-two Cohen–Macaulay surface with the forced Chern character and vanishing of all sixteen normal characteristic classes.
