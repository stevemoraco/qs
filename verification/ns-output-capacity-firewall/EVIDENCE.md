# NS output-capacity firewall — verification receipt

Date: 2026-08-13 UTC

Status: **finite Lean theorem package verified; not a Navier–Stokes theorem; six-alarm off.**

## Canonical source

- Source: `verification/ns-output-capacity-firewall/OutputCapacityFirewall.lean`
- Git blob: `5c2319aeb3feffecfac2a976f47a1870b9cc6c05`
- Source repair commit: `69f515dbac3c021dd9b197b26b07c13b00f3197c`
- Workflow pin commit: `63f934b7b53edf81797cb4dfc7ba609e9332513f`

The source has no `sorry`, `admit`, `sorryAx`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, or `Lean.ofReduceBool`. It contains seven explicit `#print axioms` commands.

## Fresh replay

- Workflow: `Verify NS output-capacity firewall`
- Run: `31678982166`
- Job: `94379848416`
- Result: `success`
- Environment: AXLE `lean-4.30.0`
- AXLE request: `34cadb62-17d3-4934-b9b4-5cdd71361709`
- AXLE executor commit: `c7ff197`
- AXLE executor image: `sha256:8c1dafc5e514f26944925383401c14fd48333d1dd9a2c77336e820c1b1e239b7`
- `okay=true`
- Lean errors: none
- Tool errors: none
- Failed declarations: none
- Warnings: none
- `sorryAx`: absent

## Axiom report

Every theorem reports exactly:

`[propext, Classical.choice, Quot.sound]`

These are the standard Mathlib/Lean foundation dependencies exposed by the proofs. No theorem-specific custom axiom occurs.

## Preserved evidence

- `evidence/axle-response.json`
- `evidence/replay-metadata.txt`
- Original artifact ID: `9172674211`
- Artifact digest: `sha256:36e046be737750e9e1ea50ef63e28f1e4eb6b769b91221746cb02f4ba601d61d`
- Downloaded raw AXLE response SHA-256: `9bc53a91a1aa01491508734bcbeee8d6236c25757a52450d7bf6b4699ae7ce9f`

## Exact theorem content

The package proves finite scalar statements only:

1. one fixed convolution output has no multiplicity gain beyond Cauchy–Schwarz;
2. `J` fixed outputs gain at most `sqrt J` in output `ℓ²` norm;
3. matching a viscous `N²` rate with a first-order `O(N)` symbol and bounded packet energies forces effective output capacity `J = Ω(N²)`;
4. when `J ≤ W³`, the packet-width tax is `W³ = Ω(N²)`;
5. the explicit scale `N=t⁴`, `W=t³` satisfies the capacity threshold for `t≥1` while `W/N=1/t`.

## What is not proved

The source does not formalize the Fourier transform, divergence-free vector fields, the Leray projector, the Euler bilinear symbol bound, lattice packet geometry, Golay leakage cancellation, Palasek shell dynamics, PDE shadowing, smooth forcing, or finite-time Navier–Stokes breakdown.

Therefore this is a verified obstruction/design constraint for the packet-embedding route, not a solution of the Clay problem.
