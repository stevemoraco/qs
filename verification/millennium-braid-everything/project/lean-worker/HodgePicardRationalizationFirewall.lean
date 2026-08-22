import Mathlib

namespace HodgePicardRationalizationFirewall

/-- The additive group `ℤ` is not 2-divisible: the equation `2 z = 1` has no
integer solution.  Any additive group underlying a `ℚ`-vector space is
2-divisible, so `ℤ` cannot be such an additive group. -/
theorem integers_not_two_divisible : ¬ ∃ z : ℤ, 2 * z = 1 := by
  norm_num

/-- Concrete degree version for `Pic(P¹) ≃ ℤ`: a degree-one class cannot be
half of another integral degree class. -/
theorem no_half_degree_one : ¬ ∃ d : ℤ, d + d = 1 := by
  norm_num

#print axioms integers_not_two_divisible
#print axioms no_half_degree_one

end HodgePicardRationalizationFirewall
