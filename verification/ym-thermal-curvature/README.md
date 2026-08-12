# Yang--Mills thermal-curvature finite verifier

**Status:** finite scalar core only; not Yang--Mills.

This pinned Lean project verifies:

- the exact finite endpoint identity
  `d_n - sum_{j < N} (d_{n+j} - d_{n+j+1}) = d_{n+N}`;
- the equivalent finite curvature-sum identity;
- the exact two-mode cross-product defect
  `w*x*y*(r-q)^2`;
- nonnegativity of the associated cross-product and logarithmic curvature;
- the exact hidden-mode mixture error `(x-y)/(w+1)`;
- positivity of the hidden coefficient at every finite nonnegative
  multiplicity;
- one exact rational hidden-mode snapshot.

## Deliberate omissions

The finite telescope is **not** an infinite endpoint theorem. Passing to
`N -> infinity` needs a separate summability and uniform-tail result.

This project does not formalize infinite series or limits, spectral measures,
Hamiltonians, transfer operators, Osterwalder--Schrader reconstruction,
lattice gauge theory, continuum limits, compact gauge groups, or the
Yang--Mills Millennium problem.

The scope is disjoint from the absolute-transfer-defect verifier in PR #142.
