# NS sideband common-heat finite-core verification receipt

Date: 2026-08-13 UTC

Status: **warning-free public Lean replay succeeded for the exact finite algebraic source only. This is not a Navier–Stokes or Clay theorem.**

## Canonical source identity

- research repository: `stevemoraco/RH-Lean`
- research branch: `agent/ns-sideband-common-heat-firewall-20260813`
- research commit: `00675a491a359baa53554b4c2308825a2feb58e1`
- source path: `Millennium/NavierStokes/SidebandCommonHeatFirewall.lean`
- canonical Git blob: `81343d9b6edfc3c9cc75c704e7468ac64aee9196`
- mirrored source SHA-256: `e5d6b91be5db825fe589fb516a048ca35f6a4f0ab2a43c84252cfcab7d417e58`

The workflow computed the mirrored Git blob and required exact equality with the canonical research blob before compiling.

## Toolchain

- Lean: `4.32.1`
- Lean commit: `f054605aea4b840552cca2e725580bffd1e1b704`
- Lake: `5.0.0-src+f054605`
- Mathlib: tag `v4.32.1`
- runner: `GitHub Actions 1000020420`
- runner image label: `ubuntu-24.04`

## Replay identity

- verifier branch: `agent/ns-sideband-common-heat-public-verifier-20260813`
- verifier commit: `37342ae5bb3e06aecfc4787f0597af63c7c9ae68`
- workflow run: `31679476935`
- job: `94381399487`
- result: `success`
- artifact: `9172918559`
- artifact digest: `sha256:605e1e067e340d40ab82a1941af2b47baef197e3bf4f635e8578ba440c5026bb`

## Trust audit

The exact compiled source contains no occurrence of:

```text
sorry
admit
sorryAx
custom axiom declaration
opaque declaration
unsafe declaration
native_decide
Lean.ofReduceBool
```

All eleven theorem declarations compiled. Every staged `#print axioms` report was exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Verified finite declarations

1. `common_heat_cancels_in_cross_numerator`
2. `exact_sideband_active_frequency_gap`
3. `optimal_coefficients_leave_unit_feedback_square`
4. `small_parent_tube_precludes_child_activation`
5. `palasek_window_implies_beta_gt_two`
6. `one_amplifier_time_rational_floor`
7. `live_point_is_inside_viscous_source_window`
8. `live_source_over_tube_exponent`
9. `live_drive_over_child_heat_exponent`
10. `live_relative_heat_over_drive_exponent`
11. `live_claimed_absolute_slaving_exponent`

## Exact boundary

The replay does not formalize the exponential ODE solution, Fourier-mode Navier–Stokes interaction table, Palasek's source theorem, packet localization, an invariant cascade, finite-time singularity, regularity, or any official Clay alternative.

**FIVE/SIX-ALARM: OFF.**
