# B5 NS recursive-relay replay — 2026-08-13

🟢 PROVED · ✅ LEAN-VERIFIED · 🧱 OBSTRUCTION

## Verified theorem package

The strengthened finite relay source proves two independent recursive leakage mechanisms for the explicit isosceles Euler/Leray atom. First, the desired `P+Q=-K` interaction produces the `N` polarization; its next interaction with `P` gives the exterior carrier `P-K=2P+Q` with exact coefficient `(0,0,2 a^2 b)`, nonzero when the selected input amplitudes `a,b` are nonzero. Second, admitting the reciprocal leaked polarization `R` reopens `P-Q`; the induced second-generation exterior coefficient is `(0,0,-b^2 c)` for nonzero `b,c`.

## Proof / derivation

The Lean source evaluates the symmetrized Euler Fourier symbol and explicit Leray projection in exact real coordinates. It also proves the full transverse-fiber decomposition at the reciprocal carrier and the nonzero coefficient consequences.

## Assumptions

Finite real carrier/polarization algebra and real amplitudes only. No time evolution, viscosity, localization, forcing, infinite cascade, or PDE regularity theorem.

## Critic verdict

🧱 The isolated three-carrier relay is not recursively support-closed with nonzero desired input amplitudes. Enlarging one polarization fiber does not fix this; it creates another leakage path. A surviving construction needs extra cancellation carriers or an invariant nonlinear coefficient manifold.

## Lean status

✅ GitHub-hosted replay run `31695967464`, job `94433697285`, completed successfully for `SixLaneAudit/NSPolarizationBundleClosure.lean` at PR head `0d7b68bdd16a00f9beed3c0a12ea2f18a4f3c68c`; the load-bearing source is commit `dc73c21aad4f5148a488b2fe69ea453180ca784b` and is unchanged at that head. Toolchain: Lean `v4.30.0`; Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Every staged theorem axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. The compiler emitted one stylistic linter warning at line 158; theorem elaboration and replay succeeded.

## Exact remaining gap

🚧 MISSING: construct and recursively verify the smallest cancellation controller that removes the forced `2 a^2 b` and reciprocal `-b^2 c` exterior terms without destroying the intended transfer; or prove a general finite-controller no-go and abandon this relay architecture.

## Provenance

Branch `agent/b5-synthesis-pointwise-uniformity-obstruction-20260813`; draft PR #308; parent hostile-surviving B5 ledger `c69b77aa6532a627888f8f3271811c64fd661829`; independently verified base relay PR #304, source blob `7dcac2d8ba0dbabf370b35d5a6463c4bdcbd8322`, run/job `31694179218` / `94428020276`.

No official Navier–Stokes theorem or disproof is closed. FIVE-ALARM remains off.
