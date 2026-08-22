# Review scope: NS output-capacity firewall

This branch adds a finite Lean theorem package and a preserved independent AXLE replay for a necessary capacity constraint in a proposed periodic Navier–Stokes shell-model embedding.

## Proved

- fixed-output Cauchy–Schwarz convolution ceiling;
- output-bundle `sqrt J` ceiling;
- necessary `J = Ω(N²)` effective-output capacity for matching an `N²` viscous rate from an `O(N)` scalar symbol with bounded packet energies;
- inherited `W³ = Ω(N²)` packet-width tax under `J ≤ W³`;
- exact parameter point `N=t⁴`, `W=t³`.

## Verification

Canonical source blob: `5c2319aeb3feffecfac2a976f47a1870b9cc6c05`.

Fresh successful AXLE Lean 4.30 replay:

- run `31678982166`;
- job `94379848416`;
- `okay=true`;
- no Lean/tool errors, failed declarations, warnings, or `sorryAx`;
- all seven theorem axiom reports are `[propext, Classical.choice, Quot.sound]`.

Raw evidence is committed under `verification/ns-output-capacity-firewall/evidence/`.

## Explicit non-claim

This branch does **not** prove Navier–Stokes breakdown, the Euler/Leray Fourier symbol bound, a lattice packet construction, a Golay vector frame, a Palasek-to-Navier–Stokes shadowing theorem, or Clay alternative D. Six-alarm is off.
