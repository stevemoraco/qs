import Mathlib

namespace NSWKBDepthDiagonal

/-- For an envelope exponent `β < 1`, choosing WKB depth above the
critical quotient forces the differentiated residual exponent negative. -/
theorem depth_makes_residual_exponent_negative
    {β q m J : ℝ}
    (hβ : β < 1)
    (hJ : (q + m) / (1 - β) < J) :
    q + m - J * (1 - β) < 0 := by
  have hden : 0 < 1 - β := sub_pos.mpr hβ
  have hmul : q + m < J * (1 - β) := (div_lt_iff₀ hden).mp hJ
  linarith

/-- The isotropic intermittency exponent `β = 2(α-1)/3` lies below one
throughout the strict physical window `α < 5/2`. -/
theorem intermittency_beta_lt_one
    {α β : ℝ}
    (hβ : β = 2 * (α - 1) / 3)
    (hα : α < (5 : ℝ) / 2) :
    β < 1 := by
  rw [hβ]
  linarith

/-- At the concrete choice `α = 9/4`, the isotropic envelope exponent is
exactly `β = 5/6`. -/
theorem alpha_nine_fourths_beta :
    2 * (((9 : ℝ) / 4) - 1) / 3 = (5 : ℝ) / 6 := by
  norm_num

/-- Consequently the WKB small-parameter exponent at `α = 9/4` is `1/6`. -/
theorem alpha_nine_fourths_wkb_slack :
    1 - (5 : ℝ) / 6 = (1 : ℝ) / 6 := by
  norm_num

/-- A convenient sufficient depth inequality at `α = 9/4`: if
`6(q+m) < J`, then the residual exponent `q+m-J/6` is negative. -/
theorem nine_fourths_depth_rule
    {q m J : ℝ}
    (hJ : 6 * (q + m) < J) :
    q + m - J * ((1 : ℝ) / 6) < 0 := by
  linarith

#print axioms depth_makes_residual_exponent_negative
#print axioms intermittency_beta_lt_one
#print axioms alpha_nine_fourths_beta
#print axioms alpha_nine_fourths_wkb_slack
#print axioms nine_fourths_depth_rule

end NSWKBDepthDiagonal
