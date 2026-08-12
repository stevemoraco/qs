# NS plane-holonomy quadratic finite replay

Public pinned replay for the exact finite source committed in `stevemoraco/RH-Lean`.

## Canonical private source

- repository: `stevemoraco/RH-Lean`
- branch: `automation/ns-plane-holonomy-quadratic-defect-firewall-20260812`
- canonical source commit: `d95e79382f6d8f3036b1335a3d7686686c000dd8`
- workflow head at mirror creation: `c21be24ab0ecd3348aab15e6bcbc12e6d9003a3e`
- path: `verification/ns-plane-holonomy/NSPlaneHolonomyQuadraticFinite.lean`
- canonical Git blob: `47042da3c3dc41e3f4b88be8c89098f547b6d2e1`

The public file is byte-for-byte identical to that source.

## Formalized statements

The Lean file proves only the scalar equal-subdivision identities:

- `N * (A/N) = A`;
- `N * (A/N)^2 = A^2/N`;
- the strict quadratic-budget implication;
- their conjunction.

These statements protect the homogeneity obstruction that a fixed first-order total displacement can coexist with an arbitrarily small summed quadratic local ledger after enough equal subdivision.

## Excluded mathematics

The replay does not formalize:

- trigonometric functions or `sin^2(A/N)`;
- Grassmannians or plane holonomy;
- Fourier modes, triads, or incompressibility;
- mode-sharing frame operators;
- the Navier–Stokes equations;
- global regularity or blow-up.

A green replay verifies only the four finite real-algebra declarations. It is not a Millennium result.
