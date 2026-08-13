import Mathlib

/-!
# Exact finite algebra behind exponential-padding exponent conservation

This is the arithmetic core of the P-vs-NP padding no-go.  If padded input
length grows like `2^(α n)` while an inherited lower bound grows like
`2^(b n)`, both exponents are rescaled by the same padding parameter.

No complexity classes are encoded here.
-/

namespace PvsNPBraid

/-- Cross-power identity expressing exact conservation of exponent ratios. -/
theorem exponential_padding_cross_power
    (α b n : ℕ) :
    (((2 : ℕ) ^ (α * n)) ^ b) = (((2 : ℕ) ^ (b * n)) ^ α) := by
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

/-- The same identity over the positive reals, useful for asymptotic wrappers. -/
theorem exponential_padding_cross_power_real
    (α b n : ℕ) :
    (((2 : ℝ) ^ (α * n)) ^ b) = (((2 : ℝ) ^ (b * n)) ^ α) := by
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

end PvsNPBraid
