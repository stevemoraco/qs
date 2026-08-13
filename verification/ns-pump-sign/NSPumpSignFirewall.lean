import Mathlib

namespace NS.PumpSignFirewall

/-- Algebraic substitution for the displayed y-pump linearization:
    x' = -a Y z, z' = c Y x implies x'' = -(a*c*Y^2) x. -/
theorem yPump_second_derivative_algebra
    (a c Y x : ℝ) :
    (-a * Y) * (c * Y * x) = -(a * c * Y^2) * x := by
  ring

/-- For positive coupling magnitudes and nonzero positive pump amplitude,
    the y-pump second-order coefficient is strictly negative. -/
theorem yPump_coefficient_negative
    (a c Y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hY : 0 < Y) :
    -(a * c * Y^2) < 0 := by
  positivity

/-- Hence the scalar characteristic equation for a real exponential growth
    rate has no real solution in the displayed y-pump linearization. -/
theorem yPump_no_real_exponential_rate
    (a c Y r : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hY : 0 < Y)
    (hr : r^2 = -(a * c * Y^2)) : False := by
  have hneg : -(a * c * Y^2) < 0 :=
    yPump_coefficient_negative a c Y ha hc hY
  have hrsq : 0 ≤ r^2 := sq_nonneg r
  nlinarith

/-- Algebraic substitution for the displayed x-pump linearization:
    y' = b X z, z' = c X y implies y'' = (b*c*X^2) y. -/
theorem xPump_second_derivative_algebra
    (b c X y : ℝ) :
    (b * X) * (c * X * y) = (b * c * X^2) * y := by
  ring

/-- The x-pump characteristic coefficient is strictly positive under the
    same positive-magnitude hypotheses. -/
theorem xPump_coefficient_positive
    (b c X : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hX : 0 < X) :
    0 < b * c * X^2 := by
  positivity

#print axioms yPump_second_derivative_algebra
#print axioms yPump_coefficient_negative
#print axioms yPump_no_real_exponential_rate
#print axioms xPump_second_derivative_algebra
#print axioms xPump_coefficient_positive

end NS.PumpSignFirewall
