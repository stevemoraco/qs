import Mathlib

/-!
# Concavity-rebate countercycle finite firewall

This file formalizes only the robust weighted three-step negativity estimate
used in the round-42 RH audit. It does not formalize square roots, logarithms,
prime arrivals, asymptotics, Johnston's criterion, zeta, or RH.
-/

namespace MillenniumBraid
namespace B2Round42RHRebate

/-- If three positive weights vary by at most a factor two and every positive
rebate is at most `d/8`, then the zero-net state cycle
`-d,-2d,0` still has strictly negative weighted increment. -/
theorem factor_two_weights_small_rebates_still_negative
    {d W A1 A2 A3 r1 r2 r3 : ℝ}
    (hd : 0 < d) (hW : 0 < W)
    (hA1lo : W ≤ A1) (hA1hi : A1 ≤ 2 * W)
    (hA2lo : W ≤ A2) (hA2hi : A2 ≤ 2 * W)
    (hA3lo : W ≤ A3) (hA3hi : A3 ≤ 2 * W)
    (hr10 : 0 ≤ r1) (hr1 : r1 ≤ d / 8)
    (hr20 : 0 ≤ r2) (hr2 : r2 ≤ d / 8)
    (hr30 : 0 ≤ r3) (hr3 : r3 ≤ d / 8) :
    A1 * (-d + r1) + A2 * (-2 * d + r2) + A3 * r3 < 0 := by
  have hW0 : 0 ≤ W := le_of_lt hW
  have h2W0 : 0 ≤ 2 * W := by positivity
  have hA10 : 0 ≤ A1 := le_trans hW0 hA1lo
  have hA20 : 0 ≤ A2 := le_trans hW0 hA2lo
  have hA30 : 0 ≤ A3 := le_trans hW0 hA3lo
  have hd8 : 0 ≤ d / 8 := by positivity
  have hb1 : A1 * r1 ≤ (2 * W) * (d / 8) := by
    exact mul_le_mul hA1hi hr1 hr10 h2W0
  have hb2 : A2 * r2 ≤ (2 * W) * (d / 8) := by
    exact mul_le_mul hA2hi hr2 hr20 h2W0
  have hb3 : A3 * r3 ≤ (2 * W) * (d / 8) := by
    exact mul_le_mul hA3hi hr3 hr30 h2W0
  have hn1 : (-d) * A1 ≤ (-d) * W := by
    exact mul_le_mul_of_nonpos_left hA1lo (le_of_lt (neg_neg_of_pos hd))
  have hn2 : (-2 * d) * A2 ≤ (-2 * d) * W := by
    have hneg : -2 * d ≤ 0 := by linarith
    exact mul_le_mul_of_nonpos_left hA2lo hneg
  have hdW : 0 < d * W := mul_pos hd hW
  nlinarith

/-- Exact algebraic decomposition into the adverse state contribution and the
positive rebate contribution. -/
theorem countercycle_rebate_decomposition
    (d A1 A2 A3 r1 r2 r3 : ℝ) :
    A1 * (-d + r1) + A2 * (-2 * d + r2) + A3 * r3 =
      -d * (A1 + 2 * A2) + (A1 * r1 + A2 * r2 + A3 * r3) := by
  ring

/-- The explicit margin in the factor-two / `d/8` regime is `9*d*W/4`. -/
theorem robust_margin_positive
    {d W : ℝ} (hd : 0 < d) (hW : 0 < W) :
    0 < 9 * d * W / 4 := by
  positivity

#print axioms factor_two_weights_small_rebates_still_negative
#print axioms countercycle_rebate_decomposition
#print axioms robust_margin_positive

end B2Round42RHRebate
end MillenniumBraid
