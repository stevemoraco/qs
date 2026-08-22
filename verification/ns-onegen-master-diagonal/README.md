# NS one-generation master diagonal replay

This directory mirrors the finite exponent core of the finite-energy one-generation AO shadowing branch.

The Lean theorem certifies only the polynomial scale compatibility after all analytic constants have been frozen. It does not formalize the PDE residual estimates, the Albritton--Ozanski unstable mode, nonlinear Navier--Stokes shadowing, regeneration, blow-up, or the Clay statement.

Pinned public replay: Lean 4.31.0 + mathlib v4.31.0. The workflow rejects `sorry`, `admit`, `sorryAx`, explicit `axiom`, `opaque`, and `unsafe` declarations and audits `#print axioms` output against the standard foundation set.
