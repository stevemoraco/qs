import Mathlib

namespace MillenniumRun14

/-- Completing the square controls a cross term by the Schur-complement penalty. -/
theorem schur_cross_term_lower_bound
    (z w gap : ℝ)
    (hgap : 0 < gap) :
    -(z ^ 2) / gap ≤ 2 * z * w + gap * w ^ 2 := by
  apply (div_le_iff₀ hgap).2
  nlinarith [sq_nonneg (gap * w + z)]

end MillenniumRun14
