# NS three-channel Gram-rank public verifier

This directory mirrors byte-for-byte the finite Lean source from:

- private repository: `stevemoraco/RH-Lean`
- research branch: `run18/ns-three-channel-rank-firewall`
- research head at mirroring: `ea1a37b7617a8b4556865e11b9fb34868a1292d2`
- source path: `lean-worker/NSChannelRankFirewall.lean`
- canonical private/public Git blob: `046a091ac0005788c87a9f3fa15cf1dd08c3aab4`
- research PR: `stevemoraco/RH-Lean#676`

The source formalizes only exact finite real-algebra statements: the singular Gram determinant for three planar channels, a weighted three-channel frame-potential identity, the equal-weight `3/4` Welch floor, the consequent half-coherent-pair disjunction, and the scalar sharpness certificate.

It does not formalize Fourier transforms, Leray projection, complex phases, triad networks, pressure, a recurrence theorem, Navier--Stokes regularity, blow-up, or either official Clay alternative.

The workflow pins Lean/Mathlib v4.32.1, verifies the exact canonical Git blob, rejects placeholders and custom trust declarations, compiles the source, prints theorem axioms, rejects `sorryAx` and `Lean.ofReduceBool`, and uploads replay evidence.
