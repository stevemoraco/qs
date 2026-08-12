# Public verifier — Navier–Stokes ancient-profile horizon finite ledger

**Status:** finite scalar replay only. **Not** a formalization of Navier–Stokes, ancient solutions, singularities, or the Clay problem.

## Canonical private provenance

- Repository/branch: `stevemoraco/RH-Lean:agent/ns-ancient-liouville-pressure-horizon-audit-20260812`
- Private note: `research/navier_stokes/NS_ANCIENT_LIOUVILLE_PRESSURE_HORIZON_AUDIT_2026-08-12.md`
- Exact Lean blob: `1d59bd69acc3a4140afe2c4617f6ca05314fdc9f`

## Replayed declarations

1. `normalized_horizon_enstrophy_identity`
2. `lifespan_floor_transfer`
3. `bounded_ratio_gives_horizon_floor`
4. `future_dissipation_scaling_identity`
5. `vanishing_tail_times_growing_amplitude`
6. `finite_or_large_horizon`

## Scope firewall

The source checks scalar identities after the analytic hypotheses are already supplied. It does not formalize:

- velocity-max rescaling as a PDE theorem;
- Sobolev inequalities or `L^6` local well-posedness;
- pressure decomposition or exclusion of parasitic solutions;
- ancient mild compactness;
- state-space tightness or endpoint singularity retention;
- the Navier–Stokes equations or the Clay theorem.

A green replay validates only the six declarations and their printed axiom reports.

Five-alarm status: OFF.
