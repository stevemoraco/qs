import Mathlib

namespace MillenniumB2Verify

/-- Correct real-interpolation weights for L^3 between L^2 and L^(10/3). -/
theorem ns_correct_l3_interpolation_weights :
    (1 / 3 : ℚ) = (1 / 6) * (1 / 2) + (5 / 6) * (3 / 10) := by
  norm_num

/-- The audited manuscript's weights (1/9,8/9) do not interpolate L^3. -/
theorem ns_wrong_l3_interpolation_weights :
    (1 / 3 : ℚ) ≠ (1 / 9) * (1 / 2) + (8 / 9) * (3 / 10) := by
  norm_num

/-- A rank-one transported quadratic form cannot dominate positive mass in a
missing coordinate. -/
theorem ym_missing_direction_blocks_upper_domination
    (a mu c b : ℝ)
    (hmu : 0 < mu) :
    ¬ (∀ x y : ℝ, a * x^2 + mu * y^2 ≤ c * b * x^2) := by
  intro h
  have hbad := h 0 1
  norm_num at hbad
  linarith

#print axioms ns_correct_l3_interpolation_weights
#print axioms ns_wrong_l3_interpolation_weights
#print axioms ym_missing_direction_blocks_upper_domination

end MillenniumB2Verify
