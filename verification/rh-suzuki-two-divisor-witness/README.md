# RH Suzuki two-divisor witness core — public replay

Date: 2026-08-13 UTC

Canonical private Lean source:

- repository: `stevemoraco/RH-Lean`
- branch: `agent/rh-suzuki-two-divisor-witness-core-20260813`
- commit: `2488f0ffd5a1f662ac9949d8230a4fc6af451149`
- path: `lean-worker/RHSuzukiTwoDivisorWitnessCore.lean`

Human theorem and hostile audit:

- repository: `stevemoraco/RH`
- branch: `agent/b2-rh-suzuki-two-divisor-ratio-repair-20260813`
- commit: `a07b6bc5af6011519e07cbcd37425e10e0a48fc3`
- path: `b2/RH_SUZUKI_TWO_DIVISOR_RATIO_REPAIR_2026-08-13.md`

This public directory mirrors the exact Lean source so a GitHub-hosted runner can install pinned Lean `v4.32.1`, compile it against Mathlib `v4.32.1`, reject proof holes and custom trust declarations, emit all eight requested `#print axioms` reports, and preserve the logs as a workflow artifact.

The formalized theorems are only the explicit witness-level terminal interface: limits of real zero witnesses remain real; zero-free families cannot transfer target zeros by actual zero witnesses; numerator and denominator carriers can be transferred separately; and the spectral coordinate `z=i(rho-1/2)` is real only on the critical line.

The source does **not** formalize spherical meromorphic convergence, Hurwitz's theorem, Suzuki's operators, the Riemann xi function, or RH. Even a green replay is not a Millennium result.
