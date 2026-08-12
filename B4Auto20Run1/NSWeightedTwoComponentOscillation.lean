import Mathlib

/-!
B4 AUTO20 run1 — Navier–Stokes weighted disconnected-component oscillation firewall.

Status at commit: 🟢 PROVED (finite scalar core) · 🔵 LEAN-SOURCE · 🟡 compile pending.
Official Millennium status: no Navier–Stokes claim.

Exact theorem identities:
* `weighted_two_component_mean_deviation_exact`
* `zero_weight_hides_arbitrary_component_jump`

Assumptions: real component values `a ≤ b` and component weight `p ∈ [0,1]`.
Provenance: current disconnected-high-set/BMO bridge and B4 AUTO19 equal-weight
counterexample. Official target remains Fefferman's Clay Navier–Stokes problem description.
Audit: no `sorry`, `admit`, `sorryAx`, custom axiom, `opaque`, or `unsafe` in this source.
Compile status at commit: pending independent runner replay.
Exact remaining gap: derive NSE-specific lower control on relevant component weights and/or
cross-component orientation, or replace this route with another global critical-scale regularity
mechanism. The scalar identity itself is not an NSE estimate.
-/

namespace B4Auto20Run1.NS

theorem weighted_two_component_mean_deviation_exact
    (p a b : ℝ)
    (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1)
    (hab : a ≤ b) :
    let μ := p * a + (1 - p) * b
    p * |a - μ| + (1 - p) * |b - μ| = 2 * p * (1 - p) * (b - a) := by
  dsimp
  have hpcomp : 0 ≤ 1 - p := by linarith
  have hleft : a - (p * a + (1 - p) * b) ≤ 0 := by
    calc
      a - (p * a + (1 - p) * b) = (1 - p) * (a - b) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpcomp (sub_nonpos.mpr hab)
  have hright : 0 ≤ b - (p * a + (1 - p) * b) := by
    calc
      0 ≤ p * (b - a) := mul_nonneg hp0 (sub_nonneg.mpr hab)
      _ = b - (p * a + (1 - p) * b) := by ring
  rw [abs_of_nonpos hleft, abs_of_nonneg hright]
  ring

theorem zero_weight_hides_arbitrary_component_jump (a b : ℝ) :
    let p : ℝ := 0
    let μ := p * a + (1 - p) * b
    p * |a - μ| + (1 - p) * |b - μ| = 0 := by
  dsimp
  simp

#print axioms weighted_two_component_mean_deviation_exact
#print axioms zero_weight_hides_arbitrary_component_jump

end B4Auto20Run1.NS
