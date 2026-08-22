import Mathlib

namespace Millennium.YangMills

theorem linear_wrapping_shifts_cubic
    (u b c k : ℝ) :
    u + b * u^2 + c * u^3 + (k * u) * u^2 =
      u + b * u^2 + (c + k) * u^3 := by
  ring

theorem linear_wrapping_is_allowed_by_first_order_schedule
    (u k : ℝ)
    (hu : 0 ≤ u)
    (hk0 : 0 ≤ k)
    (hk1 : k ≤ 1) :
    0 ≤ k * u ∧ k * u ≤ u := by
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right hk1 hu]

theorem first_order_wrapping_schedule_does_not_fix_cubic
    (u b c : ℝ) :
    u ≤ u ∧
    u + b * u^2 + c * u^3 + u * u^2 =
      u + b * u^2 + (c + 1) * u^3 := by
  constructor
  · exact le_rfl
  · ring

theorem second_order_wrapping_is_quartic
    (u δ D : ℝ)
    (hδ : |δ| ≤ D * u^2) :
    |δ * u^2| ≤ D * u^4 := by
  have hu2 : 0 ≤ u^2 := sq_nonneg u
  calc
    |δ * u^2| = |δ| * u^2 := by rw [abs_mul, abs_sq]
    _ ≤ (D * u^2) * u^2 := mul_le_mul_of_nonneg_right hδ hu2
    _ = D * u^4 := by ring

#print axioms linear_wrapping_shifts_cubic
#print axioms linear_wrapping_is_allowed_by_first_order_schedule
#print axioms first_order_wrapping_schedule_does_not_fix_cubic
#print axioms second_order_wrapping_is_quartic

end Millennium.YangMills
