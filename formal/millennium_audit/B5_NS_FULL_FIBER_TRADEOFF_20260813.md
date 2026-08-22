# B5 NS recursive relay obstruction — 2026-08-13

🟢 PROVED · 🔵 LEAN-SOURCE · 🧱 OBSTRUCTION · 🧩 BRIDGE

## Exact result

The hostile isosceles relay fails recursive closure in two independent exact ways.

**Direct active-sum leak.** With selected carriers/polarizations

`P=(1,0,0), Q=(0,1,0), K=(-1,-1,0), A=(0,1,-1), B=(-1,0,1), N=(0,0,1)`,

the desired interaction is active:

`Leray_{P+Q}(Sym(P+Q,A,B)) = (0,0,2)`.

Because `P+Q=-K`, this creates the selected `N` polarization at `-K`. At the very next bilinear generation,

`Leray_{P-K}(Sym(P-K,A,N)) = (0,0,1) ≠ 0`,

so the exterior carrier `P-K=2P+Q` is forced. With nonzero input amplitudes `a,b`, the exact next contribution is

`(0,0,2 a^2 b)`,

hence it is nonzero whenever `a,b≠0`.

**Full-fiber repair leak.** Independently, enlarging the reciprocal `P` fiber from the selected line `A` to the full transverse span of `A` and `R=(0,1,1)` reopens the conjugate-difference carrier `P-Q`: the original `A/B` pair is Leray-killed there, while `R/B` gives exactly `(0,0,-2)`. If selected `Q,K` amplitudes are `b,c`, the reciprocal interaction forces an `R` coefficient `(bc)/2`, which then produces the exterior contribution `(0,0,-b^2c)`.

## Proof / derivation

Every identity is an exact coordinate evaluation of the symmetrized Euler Fourier symbol followed by the explicit Leray projection. The source additionally proves general Leray transversality and that `A,R` span the reciprocal transverse fiber. The coefficient statements follow by direct bilinear evaluation; no asymptotic argument is used.

## Assumptions

Finite real Fourier-carrier/polarization algebra and real conjugate amplitudes. No time evolution, viscosity, localization, forcing, infinite cascade, or PDE regularity statement is assumed.

## Critic verdict

🧱 The obstruction is stronger than the earlier “one-polarization relay does not close.” Even **before** repairing the reciprocal polarization defect, the very desired `P+Q` transfer generates a mode whose next interaction with `P` leaves the triad. Thus the isolated three-carrier relay cannot be recursively closed with nonzero desired input amplitudes. The full-fiber repair supplies a second independent leakage mechanism rather than fixing the first.

The best salvage is no longer “add the missing polarization.” A viable construction must add cancellation packets/modes that remove the forced `2a²b` exterior contribution and then survive the same hostile test at every newly introduced carrier, or else prove an invariant nonlinear coefficient manifold that achieves the same cancellation.

## Lean status

🔵 LEAN-SOURCE in `SixLaneAudit/NSPolarizationBundleClosure.lean`, strengthened source commit `dc73c21aad4f5148a488b2fe69ea453180ca784b`, with staged axiom reports. The first generic Leray proof at `e007f052a25ce92c47c52483e4960633ffd329fa` failed hosted replay run/job `31695237714` / `94431418782`; it was rebuilt before the strengthened statements were added. Fresh replay is 🚧 MISSING for the current strengthened source, so no ✅ LEAN-VERIFIED claim is made yet for these new theorems.

## Exact remaining gap

🚧 MISSING: construct an enlarged recursively closed **cancellation controller** that cancels the forced exterior `2a²b` term (and the reciprocal `-b²c` term when that path is used) without destroying the intended transfer, then prove its closure under all real-conjugate interactions. If the smallest enlargement fails, formalize that failure and iterate only while the carrier graph remains finitely falsifiable.

Only after a finite controller survives recursive closure should the B5 uniform-cutoff/compactness bridge be revisited.

## Provenance

Hostile base relay independently verified in `stevemoraco/qs` PR #304, source blob `7dcac2d8ba0dbabf370b35d5a6463c4bdcbd8322`, successful run/job `31694179218` / `94428020276`. New B5 theorems are on isolated branch `agent/b5-synthesis-pointwise-uniformity-obstruction-20260813`; parent B5 ledger `c69b77aa6532a627888f8f3271811c64fd661829`.

No official Navier–Stokes theorem/disproof is closed. FIVE-ALARM remains off.
