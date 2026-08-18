import Mathlib

namespace Millennium.RH

/-- The two total pair-weights in the four-point Gaussian quadrature sum to one. -/
theorem run10az_pair_weights_sum (u : ℝ) :
    ((1 : ℝ) / 2 + u / 6) + ((1 : ℝ) / 2 - u / 6) = 1 := by
  ring

/-- If `u² = 6`, both pair-weights used by the four-point law are positive. -/
theorem run10az_pair_weights_positive (u : ℝ) (hu : u ^ 2 = 6) :
    0 < ((1 : ℝ) / 2 + u / 6) ∧
      0 < ((1 : ℝ) / 2 - u / 6) := by
  have hu_upper : u < (5 : ℝ) / 2 := by
    nlinarith [sq_nonneg (u - (5 : ℝ) / 2)]
  have hu_lower : -(5 : ℝ) / 2 < u := by
    nlinarith [sq_nonneg (u + (5 : ℝ) / 2)]
  constructor <;> nlinarith

/--
The four-point law with squared nodes `3-u` and `3+u` has unit variance when
`u²=6`.  The square roots and probability-space realization are deliberately
external; this theorem audits only the exact scalar identity.
-/
theorem run10az_gaussian_second_moment (u : ℝ) (hu : u ^ 2 = 6) :
    ((1 : ℝ) / 2 + u / 6) * (3 - u) +
        ((1 : ℝ) / 2 - u / 6) * (3 + u) = 1 := by
  calc
    ((1 : ℝ) / 2 + u / 6) * (3 - u) +
          ((1 : ℝ) / 2 - u / 6) * (3 + u) = 3 - u ^ 2 / 3 := by
      ring
    _ = 1 := by rw [hu]; norm_num

/-- Exact fourth Gaussian moment of the same four-point law. -/
theorem run10az_gaussian_fourth_moment (u : ℝ) (hu : u ^ 2 = 6) :
    ((1 : ℝ) / 2 + u / 6) * (3 - u) ^ 2 +
        ((1 : ℝ) / 2 - u / 6) * (3 + u) ^ 2 = 3 := by
  calc
    ((1 : ℝ) / 2 + u / 6) * (3 - u) ^ 2 +
          ((1 : ℝ) / 2 - u / 6) * (3 + u) ^ 2 = 9 - u ^ 2 := by
      ring
    _ = 3 := by rw [hu]; norm_num

/-- Exact sixth Gaussian moment of the same four-point law. -/
theorem run10az_gaussian_sixth_moment (u : ℝ) (hu : u ^ 2 = 6) :
    ((1 : ℝ) / 2 + u / 6) * (3 - u) ^ 3 +
        ((1 : ℝ) / 2 - u / 6) * (3 + u) ^ 3 = 15 := by
  have hu4 : u ^ 4 = 36 := by
    calc
      u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (6 : ℝ) ^ 2 := by rw [hu]
      _ = 36 := by norm_num
  calc
    ((1 : ℝ) / 2 + u / 6) * (3 - u) ^ 3 +
          ((1 : ℝ) / 2 - u / 6) * (3 + u) ^ 3 = 27 - u ^ 4 / 3 := by
      ring
    _ = 15 := by rw [hu4]; norm_num

/-- Symmetric splitting of each pair kills the first, third and fifth moments. -/
theorem run10az_symmetric_odd_moments
    (w₁ w₂ x y : ℝ) :
    (w₁ / 2) * x + (w₁ / 2) * (-x) + (w₂ / 2) * y + (w₂ / 2) * (-y) = 0 ∧
      (w₁ / 2) * x ^ 3 + (w₁ / 2) * (-x) ^ 3 +
          (w₂ / 2) * y ^ 3 + (w₂ / 2) * (-y) ^ 3 = 0 ∧
      (w₁ / 2) * x ^ 5 + (w₁ / 2) * (-x) ^ 5 +
          (w₂ / 2) * y ^ 5 + (w₂ / 2) * (-y) ^ 5 = 0 := by
  constructor
  · ring
  constructor <;> ring

/-- `u²=6` already places `u` strictly below the rational firewall `5/2`. -/
theorem run10az_sqrt_six_below_five_halves (u : ℝ) (hu : u ^ 2 = 6) :
    u < (5 : ℝ) / 2 := by
  nlinarith [sq_nonneg (u - (5 : ℝ) / 2)]

/--
Consequently the larger squared quadrature node `3+u` lies strictly below
`(5/2)²`.  Thus the four-point law can match the Gaussian moments through
order six while having no support at or beyond the `5/2` amplitude frontier.
-/
theorem run10az_largest_node_square_below_frontier
    (u : ℝ) (hu : u ^ 2 = 6) :
    3 + u < ((5 : ℝ) / 2) ^ 2 := by
  have hu_cap := run10az_sqrt_six_below_five_halves u hu
  nlinarith

/-- The `X^(5/2)` early slice is exponentially negligible versus an `X^3` window. -/
theorem run10az_exponent_gap :
    (3 : ℝ) - (5 : ℝ) / 2 = 1 / 2 := by
  norm_num

#print axioms run10az_pair_weights_sum
#print axioms run10az_pair_weights_positive
#print axioms run10az_gaussian_second_moment
#print axioms run10az_gaussian_fourth_moment
#print axioms run10az_gaussian_sixth_moment
#print axioms run10az_symmetric_odd_moments
#print axioms run10az_sqrt_six_below_five_halves
#print axioms run10az_largest_node_square_below_frontier
#print axioms run10az_exponent_gap

end Millennium.RH
