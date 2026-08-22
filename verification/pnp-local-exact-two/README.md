# Public verifier: PNP local EXACT-2 zero-excess obstruction

Status: 🔵 public replay mirror of a proved helper counterexample; **not** a P-versus-NP result.

## Private source provenance

- Repository: `stevemoraco/RH-Lean`
- Branch: `agent/pnp-local-exact-two-zero-excess-20260812`
- Private source head at mirror creation: `b3a182c3fa2aa7c57b6b5519466d3cb8d0a687ea`
- Draft PR: `stevemoraco/RH-Lean#359`
- Exact Lean blob SHA: `273aefcfeacd91cb180dd9c3ec299fd25e6991b6`
- Exact Python certificate blob SHA: `2a2ca2e7144253e4305eef4d9f27976b4cf23209`

## Theorems replayed

1. `MillenniumRun16.PNPExactTwoLocal.baseline_weight_spec`
2. `MillenniumRun16.PNPExactTwoLocal.exact_two_after_background`
3. `MillenniumRun16.PNPExactTwoLocal.background_hits_four_adjacent_layers`
4. `MillenniumRun16.PNPExactTwoLocal.four_layer_parity_threshold_factorization`
5. `MillenniumRun16.PNPExactTwoLocal.exact_two_baseline_gate_count`
6. `MillenniumRun16.PNPExactTwoLocal.exact_two_baseline_wire_ledger`
7. `MillenniumRun16.PNPExactTwoLocal.exact_two_baseline_saturates_critical_path_floor`

The Python certificate independently checks the explicit circuit semantics and graph ledger through exhaustive finite ranges.

## Scope firewall

The Lean source does not formalize Boolean circuits, normalization, critical paths, the Chen--Li--Yang theorem, probabilistic circuits, complexity classes, `P`, `NP`, or `P ≠ NP`. A successful public run verifies only the seven finite arithmetic/logical declarations under the emitted axiom report. The Python checker is exact finite computation, not a kernel proof of the universal graph theorem.

## Pinned environment

- Lean `v4.31.0`
- Mathlib `v4.31.0`

Five-alarm status: OFF.
