# Hodge Mostaed automorphic-audit public verifier

This directory mirrors byte-for-byte the finite/logical Lean source from:

- private repository: `stevemoraco/RH-Lean`
- branch: `agent/hodge-mostaed-automorphic-dimension-interior-audit-20260812-gpt56`
- commit: `c4b592ce186a0d6a14ba7a9c1deb65e97bdb2f6a`
- source path: `verification/hodge-mostaed-automorphic-audit/HodgeMostaedAutomorphicAuditFinite.lean`
- canonical Git blob: `5709ee930208c1034a6c37e25a59fe0e6a2695e1`

The source formalizes only exact dimension arithmetic, the tensor/direct-sum dimension fork, a finite block-centralizer shadow, and an abstract degree-zero non-interior countermodel. It does not formalize orthogonal Shimura varieties, theta correspondence, Arthur parameters, Rallis formulas, intersection cohomology, algebraic cycles, or the Hodge conjecture.

The workflow pins Lean/Mathlib v4.32.1, verifies the exact canonical Git blob, rejects placeholders and custom trust declarations, compiles, prints theorem axioms, rejects `sorryAx` and `Lean.ofReduceBool`, and uploads replay evidence.
