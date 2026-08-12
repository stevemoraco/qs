# Navier–Stokes projective-vorticity finite verification

This standalone Lean project checks twelve finite scalar identities used by the
projective-vorticity commutator audit:

- rank-one parallel cross-product cancellation;
- invariance after deleting a parallel component;
- coordinate action of a unit-vector projector on a collinear vector;
- three exact shear scaling identities.

It does **not** formalize Riesz transforms, BMO, Lorentz spaces, a regularity
criterion, the Navier–Stokes equations, or either official Clay alternative.

Pinned toolchain: Lean 4.32.1 and Mathlib 4.32.1.
