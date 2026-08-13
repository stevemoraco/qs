# B5 NS polarization-bundle repair — 2026-08-13

🟢 PROVED · 🔵 LEAN-SOURCE · 🧩 BRIDGE

## Corrected theorem

The reciprocal same-carrier polarization defect exposed by the hostile selective-Leray replay is not itself an infinite closure problem. At a nonzero Fourier carrier, the Leray projector lands in the carrier's transverse fiber. For the explicit reciprocal carrier in the isosceles witness, that transverse fiber is exactly spanned by the original selected polarization `isoA=(0,1,-1)` and the leaked orthogonal polarization `isoR=(0,1,1)`.

Thus upgrading that carrier from one selected line to the full two-line transverse bundle repairs **all same-carrier Leray polarization outputs** exactly.

## Proof / derivation

For `P_k(s)=s-(s·k)/(k·k) k`, direct expansion gives `k·P_k(s)=0` whenever `k·k≠0`. At the reciprocal carrier `k=(-1,0,0)`, transversality is exactly `s.x=0`. Every transverse vector `s=(0,y,z)` has the explicit decomposition

`((y-z)/2) isoA + ((y+z)/2) isoR = s`.

Therefore every Leray-projected output at this carrier lies in the two-polarization bundle. The source also reproves that `isoR` is not contained in the original `isoA` line, so one line is genuinely insufficient for this explicit relay.

## Assumptions

Finite real three-vector algebra, a nonzero carrier, and the explicit Fourier-space Leray projector. No Fourier-series convergence, Navier–Stokes time evolution, viscosity, localization, forcing, recursive packet construction, or PDE regularity theorem is assumed.

## Critic verdict

🟢 The same-carrier polarization closure debt is repaired locally by the full transverse two-dimensional fiber. 🧱 This does **not** repair cross-frequency pollution: distinct selective frames can still generate new nonzero Fourier fibers, and newly generated carriers can trigger further interactions. The hard closure debt moves from polarization dimension to the carrier-frequency interaction graph plus coefficient control.

## Lean status

🔵 LEAN-SOURCE committed at `formal/millennium_audit/SixLaneAudit/NSPolarizationBundleClosure.lean`, source commit `e007f052a25ce92c47c52483e4960633ffd329fa`. The isolated replay workflow was extended at commit `1cfc73b744febe3f59b8658203033f092b518859` to compile this source together with the two B5 uniformity files. Fresh replay is 🚧 MISSING until the workflow completes; no ✅ LEAN-VERIFIED label is claimed yet for this new theorem.

## Exact remaining gap

🚧 MISSING: construct or rule out a **recursively controlled carrier graph** whose full two-dimensional transverse fiber is allowed at each active carrier, while every newly generated carrier is either (i) already in the controlled graph, (ii) Leray-killed, or (iii) quantitatively absorbable with a uniform scale margin. Cross-frame leakage, not same-carrier polarization, is now the first finite closure gate.

After that finite graph gate, the independent B5 uniformity firewall still requires a uniform bound on scale/cutoff functions before any infinite cascade or endpoint argument can be promoted.

## Provenance

Hostile selective-Leray source/replay: `stevemoraco/qs` PR #304, source blob `7dcac2d8ba0dbabf370b35d5a6463c4bdcbd8322`, successful run/job `31694179218` / `94428020276`. Parent B5 ledger: `c69b77aa6532a627888f8f3271811c64fd661829`. Current isolated synthesis branch: `agent/b5-synthesis-pointwise-uniformity-obstruction-20260813`.

🚧 MISSING: no official Navier–Stokes theorem/disproof, and no other official Millennium theorem/disproof, is closed. FIVE-ALARM remains off.
