# B5 NS full-fiber tradeoff — 2026-08-13

🟢 PROVED · 🔵 LEAN-SOURCE · 🧱 OBSTRUCTION · 🧩 BRIDGE

## Exact result

The obvious repair of the isosceles reciprocal polarization leak—enlarge the `P` carrier from the selected line `A=(0,1,-1)` to the full transverse span of `A` and `R=(0,1,1)`—creates a new exact failure: the added `R` line reopens the conjugate-difference carrier `P-Q` that the original selected `A/B` pair killed.

For

`P=(1,0,0)`, `Q=(0,1,0)`, `B=(-1,0,1)`,

the original pair satisfies

`Leray_{P-Q}(Sym(P-Q,A,B)) = 0`,

while the added leaked line satisfies

`Leray_{P-Q}(Sym(P-Q,R,B)) = (0,0,-2) ≠ 0`.

## Proof / derivation

Both identities are direct exact evaluations of the symmetrized Euler Fourier symbol followed by the explicit Leray projection. The same source also proves that `A,R` span the entire reciprocal transverse fiber, so this is not a basis-choice artifact: admitting the whole fiber necessarily admits the explicit `R` direction that activates the exterior difference with `B`.

## Assumptions

Finite real Fourier-carrier/polarization algebra only. No time evolution, viscosity, localization, forcing, infinite cascade, or regularity statement is used.

## Critic verdict

🧱 The naive synthesis “repair reciprocal leakage by allowing the full transverse fiber, then retain the old frequency selectivity” is false for the explicit relay. Same-carrier polarization closure and conjugate-difference frequency cancellation trade off. The surviving route must use coefficient constraints/cancellations, extra packets, or an enlarged but quantitatively controlled carrier graph rather than unconstrained full fibers.

## Lean status

🔵 LEAN-SOURCE in `SixLaneAudit/NSPolarizationBundleClosure.lean`, commit `7ab75413057a3a3a5af2b091ee3073cfd6a92fb5`, with staged axiom reports. Fresh replay is 🚧 MISSING for this strengthened source.

## Exact remaining gap

🚧 MISSING: find a recursively closed **state manifold**, not merely a support set: it must contain the reciprocal leakage direction while enforcing coefficient relations that cancel or absorb the newly activated `P-Q` exterior mode, and those relations must propagate under every subsequent interaction. If no such finite-dimensional manifold exists, formalize the corresponding no-go and abandon this relay architecture.

## Provenance

Hostile base relay is independently verified in `stevemoraco/qs` PR #304, source blob `7dcac2d8ba0dbabf370b35d5a6463c4bdcbd8322`, run/job `31694179218` / `94428020276`. New B5 theorem is on isolated branch `agent/b5-synthesis-pointwise-uniformity-obstruction-20260813`; parent ledger `c69b77aa6532a627888f8f3271811c64fd661829`.

No official Navier–Stokes theorem/disproof is closed. FIVE-ALARM remains off.
