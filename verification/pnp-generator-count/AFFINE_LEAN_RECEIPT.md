# PNP affine-slice finite core — Lean receipt

- Workflow run: 31544839849
- Job attempt: 1
- Verified commit: b7227802616c2a0980166d51b93127c53a0b24dc
- Repository: stevemoraco/qs
- Ref: refs/heads/pnp/generator-count-capacity-public-verify-20260811
- Lean: Lean (version 4.32.1, x86_64-unknown-linux-gnu, commit f054605aea4b840552cca2e725580bffd1e1b704, Release)
- Mathlib resolved revision: 
- Explicit placeholder scan: passed
- Compiler placeholder scan: passed

## Printed theorem axiom report

```
'PNP.AffineSliceCapacity.sliceStateValues_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PNP.AffineSliceCapacity.represented_slice_values_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PNP.AffineSliceCapacity.no_represented_set_above_affine_slice_capacity' depends on axioms: [propext,
'PNP.AffineSliceCapacity.coarse_affine_rank_budget_contradiction' depends on axioms: [propext, Quot.sound]
```

## Boundary

This receipt verifies only : finite slice-state image cardinality, represented-set consequence, impossibility above capacity, and the coarse scalar endpoint. It does not verify affine dimension, pivot projections, row-sum encoding, the external paper, asymptotics, arithmetic complexity, VP/VNP, or P versus NP.
