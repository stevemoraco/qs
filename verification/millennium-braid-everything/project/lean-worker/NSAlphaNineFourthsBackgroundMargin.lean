import Mathlib

namespace NSAlphaNineFourthsBackgroundMargin

/-- Exact quadratic form of the worst-case background-transport exponent margin. -/
theorem background_margin_identity (b : ℝ) :
    (5:ℝ)/4 + (2*b-1)*(2*b-(9:ℝ)/4)
      = 1 + (3:ℝ)/2*(b-1) + 4*(b-1)^2 := by ring

/-- The worst-case background margin is strictly larger than one for b>1. -/
theorem background_margin_lower {b : ℝ} (hb : 1 < b) :
    1 < (5:ℝ)/4 + (2*b-1)*(2*b-(9:ℝ)/4) := by
  rw [background_margin_identity]
  have ht : 0 < b-1 := sub_pos.mpr hb
  nlinarith [sq_nonneg (b-1)]

/-- With beta>2b, the actual alpha=9/4 background-transport gap is larger still. -/
theorem background_gap_pos
    {beta b : ℝ} (hb : 1 < b) (hbeta : 2*b < beta) :
    1 < (5:ℝ)/4 + (2*b-1)*(beta-(9:ℝ)/4) := by
  have hc : 0 < 2*b-1 := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hbeta hc
  have hbase := background_margin_lower hb
  nlinarith

#print axioms background_margin_identity
#print axioms background_margin_lower
#print axioms background_gap_pos

end NSAlphaNineFourthsBackgroundMargin
