import Mathlib

/-!
B4 AUTO19 run8 — Navier–Stokes disconnected-high-set oscillation firewall.

Status at commit: 🟢 PROVED (finite scalar core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no Navier–Stokes claim.

Exact theorem identities:
* `opposite_two_point_mean_is_zero`
* `opposite_two_point_mean_deviation_is_full_amplitude`
* `zero_componentwise_variation_can_coexist_with_order_one_global_oscillation`

Assumptions: scalar two-component model only. It is the exact arithmetic core of the
counterexample where disconnected components can each be constant while their union has
order-one mean oscillation.
Provenance: current Navier–Stokes disconnected-high-set firewall mirrored in qs PR #151.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: derive an equation-specific geometric/analytic mechanism controlling
cross-component oscillation (or replace that route entirely); componentwise local smoothness
alone does not give the global BMO-type smallness needed by the proposed bridge.
-/

namespace B4Auto19Run8.NS

theorem opposite_two_point_mean_is_zero (a : ℝ) :
    (a + (-a)) / 2 = 0 := by
  ring

theorem opposite_two_point_mean_deviation_is_full_amplitude (a : ℝ) :
    (|a| + |-a|) / 2 = |a| := by
  rw [abs_neg]
  ring

theorem zero_componentwise_variation_can_coexist_with_order_one_global_oscillation :
    ∃ a b meanDev : ℝ,
      a = 1 ∧
      b = -1 ∧
      (a + b) / 2 = 0 ∧
      meanDev = (|a| + |b|) / 2 ∧
      meanDev = 1 := by
  refine ⟨1, -1, 1, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms opposite_two_point_mean_is_zero
#print axioms opposite_two_point_mean_deviation_is_full_amplitude
#print axioms zero_componentwise_variation_can_coexist_with_order_one_global_oscillation

end B4Auto19Run8.NS
