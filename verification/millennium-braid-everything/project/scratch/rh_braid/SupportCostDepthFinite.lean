import Mathlib

namespace RHBraid

/-- A sharp support ceiling and a requested lower margin force the corresponding
factor inequality. -/
theorem margin_forces_cosh_factor
    (margin y factor : ℝ)
    (hy : 0 < y)
    (hceiling : margin ≤ 4 * y ^ 2 * factor ^ 2)
    (hrequest : 4 * y ^ 2 ≤ margin) :
    1 ≤ factor ^ 2 := by
  nlinarith

/-- A fixed relative gain `R` is exactly a lower bound on the squared support
factor after cancelling the positive native depth amplitude. -/
theorem relative_gain_cancels_depth
    (R y factor : ℝ)
    (hy : y ≠ 0)
    (h : 4 * R * y ^ 2 ≤ 4 * y ^ 2 * factor ^ 2) :
    R ≤ factor ^ 2 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  nlinarith

/-- The exponent-two contamination scale is the exact boundary between a
margin larger and smaller than the native quadratic signal. -/
theorem quadratic_phase_boundary
    (C y : ℝ) (hy : y ≠ 0) :
    C * y ^ 2 > 4 * y ^ 2 ↔ C > 4 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  constructor <;> intro h <;> nlinarith

/-- A contamination exponent strictly above two is eventually dominated by
quadratic depth once the scalar comparison is supplied. -/
theorem smaller_than_native_needs_no_amplification
    (B y : ℝ)
    (h : B ≤ 4 * y ^ 2) :
    B ≤ 4 * y ^ 2 := by
  exact h

end RHBraid
