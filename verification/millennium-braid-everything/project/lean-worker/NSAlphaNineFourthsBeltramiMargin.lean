import Mathlib

namespace NSAlphaNineFourthsBeltramiMargin

/-- The alpha=9/4 localization bandwidth exponent is exactly 5/6. -/
theorem localization_exponent :
    2*(((9:ℝ)/4)-1)/3 = (5:ℝ)/6 := by norm_num

/-- Completing the square gives the uniform lower bound used in the recursive modulation margin. -/
theorem quadratic_margin_identity (t : ℝ) :
    (1:ℝ)/6 + 4*t^2 - t/2
      = 4*(t-(1:ℝ)/16)^2 + (29:ℝ)/192 := by ring

/-- The worst-case lower envelope of the modulation margin is at least 29/192. -/
theorem quadratic_margin_lower (t : ℝ) :
    (29:ℝ)/192 ≤ (1:ℝ)/6 + 4*t^2 - t/2 := by
  rw [quadratic_margin_identity]
  nlinarith [sq_nonneg (t-(1:ℝ)/16)]

/-- In the alpha=9/4 Palasek window, the next-shell stress exponent strictly beats the modulated-Beltrami residual exponent by more than 29/192. -/
theorem beltrami_next_shell_margin
    {beta b : ℝ}
    (hb : 1 < b)
    (hbeta : 2*b < beta) :
    (29:ℝ)/192 < (1:ℝ)/6 + 2*(beta-(9:ℝ)/4)*(b-1) := by
  let t : ℝ := b-1
  have ht : 0 < t := sub_pos.mpr hb
  have hmul :
      2*((2*b)-(9:ℝ)/4)*(b-1)
        < 2*(beta-(9:ℝ)/4)*(b-1) := by
    have := mul_lt_mul_of_pos_right hbeta ht
    nlinarith
  have hbase :
      (29:ℝ)/192 ≤ (1:ℝ)/6 + 2*((2*b)-(9:ℝ)/4)*(b-1) := by
    have hq := quadratic_margin_lower t
    dsimp [t] at hq
    nlinarith
  linarith

#print axioms localization_exponent
#print axioms quadratic_margin_identity
#print axioms quadratic_margin_lower
#print axioms beltrami_next_shell_margin

end NSAlphaNineFourthsBeltramiMargin
