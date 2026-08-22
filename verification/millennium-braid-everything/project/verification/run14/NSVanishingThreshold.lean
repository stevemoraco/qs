import Mathlib

namespace MillenniumRun14

/-- A nonnegative scalar below every positive threshold is exactly zero. -/
theorem ns_zero_of_le_every_positive_threshold
    (x : ℝ)
    (hx : 0 ≤ x)
    (h : ∀ tau : ℝ, 0 < tau → x ≤ tau) :
    x = 0 := by
  by_contra hne
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have hhalf := h (x / 2) (by linarith)
  linarith

end MillenniumRun14
