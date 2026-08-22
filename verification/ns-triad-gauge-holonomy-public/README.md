# NS triad gauge-holonomy public verifier

This directory mirrors byte-for-byte the finite Lean source from:

- private repository: `stevemoraco/RH-Lean`
- research branch: `run19/ns-triad-gauge-holonomy`
- research head at mirroring: `d7411b552788aeadbd90fd4298ae4579bc34add3`
- source path: `lean-worker/NSTriadHolonomyFirewall.lean`
- canonical private/public Git blob: `358f1669ffc4ae40ecd193aa7b186d5ea56385ce`
- research PR: `stevemoraco/RH-Lean#691`

The source formalizes only exact finite group identities: triangle coboundary holonomy, obstruction by nontrivial cycle product, exact realizability of a two-edge chain, gauge conjugation of cycle holonomy, the additive triangle identity, and a `ZMod 4` three-quarter-turn countermodel.

It does not define a Fourier-triad connection or groupoid, derive edge transforms from the Euler trilinear form, prove that recurrence forces a cycle, prove Navier--Stokes regularity or blow-up, or establish either official Clay alternative.

The workflow pins Lean/Mathlib v4.32.1, verifies the exact canonical Git blob, rejects placeholders and custom trust declarations, compiles the source, prints theorem axioms, rejects `sorryAx` and `Lean.ofReduceBool`, and uploads replay evidence.
