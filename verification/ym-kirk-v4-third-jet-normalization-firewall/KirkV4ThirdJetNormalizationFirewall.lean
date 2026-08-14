import Mathlib

namespace Millennium.YangMills

/-- Scalar model for a parabolic weak-coupling step through cubic order. -/
def cubicRGMap (b c u : ℝ) : ℝ :=
  u + b * u^2 + c * u^3

/-- Two reduced maps may have the same linear and quadratic terms while differing
by an arbitrary cubic coefficient. Their difference is exactly `k u^3`. -/
theorem cubic_coefficient_shift_is_exactly_cubic
    (b c k u : ℝ) :
    cubicRGMap b (c + k) u - cubicRGMap b c u = k * u^3 := by
  simp [cubicRGMap]
  ring

/-- Explicit hostile model for a two-jet / `O(u^3)` comparison: shifting the
cubic coefficient by one changes the map by exactly `u^3`. -/
theorem cubic_order_comparison_does_not_fix_cubic_coefficient
    (b c u : ℝ) :
    cubicRGMap b (c + 1) u - cubicRGMap b c u = u^3 := by
  simpa using cubic_coefficient_shift_is_exactly_cubic b c 1 u

/-- The same hostile model satisfies the sharp cubic absolute-value envelope. -/
theorem unit_cubic_shift_fits_cubic_absolute_bound
    (b c u : ℝ) :
    |cubicRGMap b (c + 1) u - cubicRGMap b c u| = |u|^3 := by
  rw [cubic_order_comparison_does_not_fix_cubic_coefficient]
  exact abs_pow u 3

/-- By contrast, a quartic perturbation does not alter the displayed cubic
coefficient: it is separated into a genuine `u^4` remainder. -/
theorem quartic_remainder_keeps_cubic_term
    (b c r u : ℝ) :
    cubicRGMap b c u + r * u^4 =
      u + b * u^2 + c * u^3 + r * u^4 := by
  rfl

#print axioms cubic_coefficient_shift_is_exactly_cubic
#print axioms cubic_order_comparison_does_not_fix_cubic_coefficient
#print axioms unit_cubic_shift_fits_cubic_absolute_bound
#print axioms quartic_remainder_keeps_cubic_term

end Millennium.YangMills
