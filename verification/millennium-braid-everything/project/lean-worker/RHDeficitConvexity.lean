import Mathlib

namespace RHDeficitConvexity

/-- Algebraic positivity behind strict convexity of the weighted-Chebyshev
deficit on an interval where the endpoint staircase values are fixed. -/
theorem smooth_piece_curvature_positive
    {x A1 A2 : ℝ}
    (hx : 0 < x)
    (hA1 : 0 ≤ A1)
    (hmono : A1 ≤ A2) :
    0 < x ^ (- (3 : ℤ) / 2 : ℝ) + (2 + 2 * A2 - A1) / x^2 := by
  have hcoef : 0 < 2 + 2 * A2 - A1 := by linarith
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have hterm2 : 0 < (2 + 2 * A2 - A1) / x^2 := div_pos hcoef hx2
  have hterm1 : 0 < x ^ (- (3 : ℤ) / 2 : ℝ) := by positivity
  linarith

/-- Normalized full-knot jump is positive whenever the prime-power square root
exceeds two. The positive logarithmic/prime factors are abstracted into `c`. -/
theorem full_knot_jump_positive
    {c y : ℝ}
    (hc : 0 < c)
    (hy : 2 < y) :
    0 < c * (y - 2) := by
  positivity

/-- Every half-odd activation jump has negative sign once its weight is
positive. -/
theorem half_odd_jump_negative
    {c : ℝ}
    (hc : 0 < c) :
    -2 * c < 0 := by
  linarith

#print axioms smooth_piece_curvature_positive
#print axioms full_knot_jump_positive
#print axioms half_odd_jump_negative

end RHDeficitConvexity
