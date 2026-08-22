import Mathlib

namespace RHOddPrimeGap

/-- If `ell < 1` and `w > 0`, the sole-shift quadratic contribution
`-2*w*(1-ell)` is strictly negative. -/
theorem sole_shift_is_negative
    (ell w : ℝ)
    (hell1 : ell < 1)
    (hw : 0 < w) :
    -2 * w * (1 - ell) < 0 := by
  have hgap : 0 < 1 - ell := by linarith
  have hprod : 0 < w * (1 - ell) := mul_pos hw hgap
  nlinarith

/-- A fixed negative test value rules out any lower bound of the form `>= -eps`
when `eps` is smaller than its absolute margin. -/
theorem fixed_negative_kills_small_error
    (c eps q : ℝ)
    (hsmall : eps < c)
    (hq : q ≤ -c) :
    ¬ (-eps ≤ q) := by
  intro h
  linarith

#print axioms sole_shift_is_negative
#print axioms fixed_negative_kills_small_error

end RHOddPrimeGap
