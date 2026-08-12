# NS spherical-curvature holonomy public verifier

This directory mirrors byte-for-byte the finite Lean source from:

- private repository: `stevemoraco/RH-Lean`
- research branch: `run20/ns-spherical-curvature-holonomy`
- research head at mirroring: `71197f548c913c48c43f59bd1056b2cfb901fe05`
- source path: `lean-worker/NSSphericalHolonomyFirewall.lean`
- canonical private/public Git blob: `071b0e694f4ad9347222ad68b0fad8a0ec8ee1fc`

The source formalizes only exact coordinate linear algebra: three right-angle orthogonal transport matrices, their action on coordinate normals, their nontrivial quarter-turn cycle product, and exact cancellation after dividing by the geometric holonomy.

It does not prove a general Gauss--Bonnet theorem, construct a Fourier-triad connection, derive an interaction transport from the Euler trilinear form, prove recurrence forces a loop, prove Navier--Stokes regularity or blow-up, or establish either official Clay alternative.

The workflow pins Lean/Mathlib v4.32.1, verifies the exact canonical Git blob, rejects placeholders and custom trust declarations, compiles the source, prints theorem axioms, rejects `sorryAx` and `Lean.ofReduceBool`, and uploads replay evidence.
