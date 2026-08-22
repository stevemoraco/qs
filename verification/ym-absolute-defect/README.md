# Yang--Mills absolute-defect finite verifier

**Status:** finite scalar core only; not Yang--Mills.

This pinned Lean project checks:

- a finite nonnegative loss need not leave a positive remainder;
- a lower scalar/form comparison cannot be read as a reverse upper comparison;
- a nonnegative gap does not bound `exp(a * gap)` by `exp(a)`;
- keeping a transfer eigenvalue fixed while doubling physical time halves the generator gap;
- the first exact rational transfer recursions and absolute/relative defect values in the countermodel;
- the first physical-gap coefficients decrease.

The workflow pins Lean and Mathlib `v4.32.1`, rejects explicit `sorry`, `admit`, custom `axiom`, and native decision artifacts, compiles the exact source, prints theorem axioms, scans for `sorryAx`, and uploads the compiler log.

It does not formalize infinite sums or limits, transfer-operator spectral calculus, Osterwalder--Schrader reconstruction, lattice gauge theory, renormalization, compact gauge groups, or the Yang--Mills Millennium problem.
