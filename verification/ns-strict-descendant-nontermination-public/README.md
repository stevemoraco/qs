# NS strict-descendant nontermination public verifier

This directory mirrors byte-for-byte the finite/logical Lean source from:

- private repository: `stevemoraco/RH-Lean`
- branch: `agent/ns-strict-descendant-nontermination-20260812-gpt56`
- commit: `b5fde41d6c9d3ffe25b79e6bb37c014da1b6f635`
- source path: `verification/ns-strict-descendant-nontermination/NSStrictDescendantNontermination.lean`
- canonical Git blob: `af1851b6c2d06de45e260ac3dbb900304aa920fa`

The source formalizes only the abstract infinite constant-rank descendant chain and the failure of a one-step descendant-or-exit disjunction to imply termination. It does not formalize Shahmurov's packet construction, Navier–Stokes equations, singularities, axisymmetric regularity, or the Clay problem.

The workflow pins Lean/Mathlib v4.32.1, verifies the exact canonical Git blob, rejects placeholders and custom trust declarations, compiles, prints theorem axioms, rejects `sorryAx` and `Lean.ofReduceBool`, and uploads the replay evidence.
