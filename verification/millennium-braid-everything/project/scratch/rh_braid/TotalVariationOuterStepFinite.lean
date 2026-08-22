import Mathlib

/-!
# Scalar core of total-variation optimality for the outer centered difference

This file formalizes only the finite order algebra behind the signed-measure
extremal theorem. It does not formalize signed Borel measures, Fourier
transforms, the zeta zero sum, the explicit formula, or RH.
-/

namespace RHProof
namespace TotalVariationOuterStep

/-- Equal positive/negative Jordan masses `m`, positive-part average at least
`lo`, and negative-part average at most `hi` imply the sharp oscillation bound.
-/
theorem equal_mass_range_bound
    (m pos neg lo hi : ℝ)
    (hm : 0 ≤ m)
    (hpos : m * lo ≤ pos)
    (hneg : neg ≤ m * hi) :
    neg - pos ≤ m * (hi - lo) := by
  nlinarith

/-- Hyperbolic specialization of the range bound after inserting
`lo = 1`, `hi = W`. -/
theorem zero_mass_total_variation_bound
    (C pos neg W : ℝ)
    (hC : 0 ≤ C)
    (hpos : C / 2 ≤ pos)
    (hneg : neg ≤ (C / 2) * W) :
    neg - pos ≤ (C / 2) * (W - 1) := by
  have hm : 0 ≤ C / 2 := by positivity
  nlinarith

/-- The centered outer step saturates the scalar bound. -/
theorem outer_step_saturates (C W : ℝ) :
    (C / 2) * W - C / 2 = (C / 2) * (W - 1) := by
  ring

/-- Equivalent `sinh²` form after the identity
`cosh(2a)-1 = 2 sinh²(a)` is supplied by the analytic layer. -/
theorem cosh_to_sinh_cost_form
    (C q : ℝ) (hidentity : q - 1 = 2 * ((q - 1) / 2)) :
    (C / 2) * (q - 1) = C * ((q - 1) / 2) := by
  ring

/-- Any strict interior placement of negative mass loses against the endpoint
when the endpoint weight is strictly larger. -/
theorem strict_loss_away_from_endpoint
    (m w W : ℝ)
    (hm : 0 < m) (hw : w < W) :
    m * w - m < m * W - m := by
  nlinarith

/-- The Chebyshev `l1` no-go is a direct numerical corollary of a universal
cost-normalized bound: if a candidate signal is strictly below `m²` times the
outer signal while its cost is exactly `m²` times larger, its normalized
signal is strictly worse. -/
theorem normalized_signal_strictly_worse
    (signal outer cost : ℝ) (m : ℕ)
    (houter : 0 < outer) (hcost : 0 < cost)
    (hm : 0 < m)
    (hsignal : signal < (m : ℝ)^2 * outer) :
    signal / ((m : ℝ)^2 * cost) < outer / cost := by
  have hmreal : 0 < (m : ℝ)^2 := by positivity
  rw [div_lt_div_iff₀ (mul_pos hmreal hcost) hcost]
  nlinarith

end TotalVariationOuterStep
end RHProof
