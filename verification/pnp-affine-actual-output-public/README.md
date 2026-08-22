# PNP affine-refuter actual-output public verifier

This directory mirrors byte-for-byte the finite Lean source from:

- private repository: `stevemoraco/RH-Lean`
- branch: `agent/pnp-affine-refuter-actual-output-family-20260812-gpt56`
- research head at mirroring: `d9d1acdadefa97fe850b6b86a87325fa0d602c15`
- source path: `verification/pnp-affine-actual-output/PNPAffineActualOutputFinite.lean`
- canonical Git blob: `87b600768f3b58e41db80a01936bc64de34a06be`

The source formalizes only assignment cardinality, coordinate-fiber uniqueness/nonemptiness, a finite surjective-label lower bound, and scalar gate/measure budgets. It does not formalize Boolean circuits, Carmosino--Dang--Jackman Algorithm 2, sparse languages, hardness magnification, NP, or P versus NP.

The workflow pins Lean/Mathlib v4.32.1, verifies the exact private Git blob, rejects placeholders and custom trust declarations, compiles, records theorem axioms, rejects `sorryAx` and `Lean.ofReduceBool`, and uploads replay evidence.
