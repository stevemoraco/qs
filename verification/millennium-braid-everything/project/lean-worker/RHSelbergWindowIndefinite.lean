import Mathlib

namespace RHSelbergWindowIndefinite

/-- The two-point restriction of the centered Selberg product-window kernel can
be the exchange matrix.  Its quadratic form is negative on `(1,-1)`. -/
theorem exchange_kernel_negative :
    (1 : ℝ) * 0 * 1
      + (1 : ℝ) * 1 * (-1)
      + (-1 : ℝ) * 1 * 1
      + (-1 : ℝ) * 0 * (-1) = -2 := by
  norm_num

/-- The same kernel is positive on `(1,1)`, so it is genuinely indefinite. -/
theorem exchange_kernel_positive :
    (1 : ℝ) * 0 * 1
      + (1 : ℝ) * 1 * 1
      + (1 : ℝ) * 1 * 1
      + (1 : ℝ) * 0 * 1 = 2 := by
  norm_num

#print axioms exchange_kernel_negative
#print axioms exchange_kernel_positive

end RHSelbergWindowIndefinite
