# BSD odd-shift duality finite verifier

**Status:** finite algebraic core only; not BSD.

This pinned Lean project checks:

- invariance plus norm one implies square one;
- square one in a domain implies `±1`;
- sign removal requires a specialization that distinguishes `-1` from `1`;
- reduction modulo two does not distinguish those signs;
- an explicit finite truncated-polynomial involution admits a nontrivial invariant unit of augmentation one whose involutive norm is not one;
- the scalar parity exponents for shifts three and two.

It does not formalize determinant functors, perfect derived categories, Selmer complexes, Iwasawa algebras, the Macias Castillo--Sano self-duality, the Burns--Sano functional equation, Sano's leading-term equation, elliptic curves, or the Birch--Swinnerton-Dyer conjecture.

The workflow pins Lean and Mathlib `v4.32.1`, rejects explicit `sorry`, `admit`, and custom `axiom` declarations, compiles the exact source, prints theorem axioms, scans the compiler output for `sorryAx`, and uploads the log.
