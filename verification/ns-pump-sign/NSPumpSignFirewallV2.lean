import Mathlib

namespace NS.PumpSignFirewall

theorem yPump_second_derivative_algebra_v2
    (a c Y x : ℝ) :
    (-a * Y) * (c * Y * x) = -(a * c * Y^2) * x := by
  ring

theorem yPump_coefficient_negative_v2
    (a c Y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hY : 0 < Y) :
    -(a * c * Y^2) < 0 := by
  have hpos : 0 < a * c * Y^2 := by
    positivity
  linarith

theorem yPump_no_real_exponential_rate_v2
    (a c Y r : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hY : 0 < Y)
    (hr : r^2 = -(a * c * Y^2)) : False := by
  have hneg : -(a * c * Y^2) < 0 :=
    yPump_coefficient_negative_v2 a c Y ha hc hY
  have hrsq : 0 ≤ r^2 := sq_nonneg r
  nlinarith

theorem xPump_second_derivative_algebra_v2
    (b c X y : ℝ) :
    (b * X) * (c * X * y) = (b * c * X^2) * y := by
  ring

theorem xPump_coefficient_positive_v2
    (b c X : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hX : 0 < X) :
    0 < b * c * X^2 := by
  positivity

#print axioms yPump_second_derivative_algebra_v2
#print axioms yPump_coefficient_negative_v2
#print axioms yPump_no_real_exponential_rate_v2
#print axioms xPump_second_derivative_algebra_v2
#print axioms xPump_coefficient_positive_v2

end NS.PumpSignFirewall
