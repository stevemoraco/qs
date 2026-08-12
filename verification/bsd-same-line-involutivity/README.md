# BSD same-line involutivity finite verifier

**Status:** finite scalar and rank-one hyperbolic core only; not BSD.

This pinned Lean project checks:

- an involutive semilinear coordinate model when its operator multiplier has
  involutive norm one;
- the change-of-generator law;
- an involution-fixed scale preserves the same-line multiplier;
- an exact rational countermodel in which an involutive same-line map gives
  two generators the same multiplier although their ratio is not norm one;
- preservation of the rank-one hyperbolic pairing;
- the corresponding determinant-coordinate norm scaling.

It does not formalize determinant functors, derived categories, Selmer
complexes, Iwasawa algebras, the Macias Castillo--Sano or Burns--Sano maps,
Sano equation (5.4.4), elliptic curves, or BSD.

The workflow pins Lean and Mathlib `v4.32.1`, rejects explicit placeholders
and custom axiom declarations, compiles the exact source, prints theorem
axioms, scans the output for `sorryAx`, and uploads the compiler log.
