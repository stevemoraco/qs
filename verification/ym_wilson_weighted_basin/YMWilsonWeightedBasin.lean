import Mathlib

namespace YMWilsonWeightedBasin

/-- If the diagonal Hessian row costs at most `2 x` and the off-diagonal row
costs at most `6 x`, multiplying the off-diagonal part by a nonnegative weight
`w` gives the exact Wilson weighted-row envelope `2 x (1 + 3 w)`. -/
theorem weighted_row_from_diag_offdiag
    {diag off x w : ℝ}
    (hdiag : diag ≤ 2 * x)
    (hoff : off ≤ 6 * x)
    (hw : 0 ≤ w) :
    diag + w * off ≤ 2 * x * (1 + 3 * w) := by
  calc
    diag + w * off ≤ 2 * x + w * (6 * x) :=
      add_le_add hdiag (mul_le_mul_of_nonneg_left hoff hw)
    _ = 2 * x * (1 + 3 * w) := by ring

/-- At weight one, the normalized weighted-C2 basin condition is exactly the
usual strict `16 x < 1` strong-coupling inequality. -/
theorem strong_threshold_is_unweighted_open_basin
    {x : ℝ}
    (hstrong : 16 * x < 1) :
    2 * x * (1 + 3 * (1 : ℝ)) < (1 : ℝ) / 2 := by
  nlinarith

/-- The half-threshold `x ≤ 1/32` admits the explicit weight `w=2` with a
strict `7/16 < 1/2` normalized curvature margin.  Analytically `w=exp μ`, so
this is the finite arithmetic core behind the choice `μ=log 2`. -/
theorem half_threshold_accepts_weight_two
    {x : ℝ}
    (hx : 0 ≤ x)
    (hhalf : x ≤ (1 : ℝ) / 32) :
    2 * x * (1 + 3 * (2 : ℝ)) < (1 : ℝ) / 2 := by
  nlinarith

/-- Quantitative version of the preceding theorem: at the closed half-threshold
with weight two, the normalized Hessian row is at most `7/16`. -/
theorem half_threshold_weight_two_margin
    {x : ℝ}
    (hhalf : x ≤ (1 : ℝ) / 32) :
    2 * x * (1 + 3 * (2 : ℝ)) ≤ (7 : ℝ) / 16 := by
  nlinarith

#print axioms weighted_row_from_diag_offdiag
#print axioms strong_threshold_is_unweighted_open_basin
#print axioms half_threshold_accepts_weight_two
#print axioms half_threshold_weight_two_margin

end YMWilsonWeightedBasin
