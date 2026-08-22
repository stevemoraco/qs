import Mathlib

/-!
# RH dyadic fine-scale transfer: finite arithmetic core

Honesty status: this file formalizes only finite rational/geometric-series and
scale-bookkeeping statements used in the analytic research note.  It does not
formalize B-spline functions, convolution, Jensen's inequality in function
spaces, the prime number theorem, the Selberg integral, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHDyadicTransferFinite

/-- The nine order-eight refinement weights have total numerator `2^8`. -/
theorem binomialEightMass :
    (1 : ℚ) + 8 + 28 + 56 + 70 + 56 + 28 + 8 + 1 = 2 ^ 8 := by
  norm_num

/-- Exact finite geometric sum controlling the accumulated dyadic shifts. -/
theorem dyadicGeometricSum (m : ℕ) :
    (∑ j ∈ Finset.range m, (1 / 2 : ℚ) ^ j)
      = 2 * (1 - (1 / 2 : ℚ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- The exact support radius after `m` refinements, in units of the base width. -/
theorem dyadicSupportRadius (m : ℕ) :
    4 * (∑ j ∈ Finset.range m, (1 / 2 : ℚ) ^ j)
      = 8 * (1 - (1 / 2 : ℚ) ^ m) := by
  rw [dyadicGeometricSum]
  ring

/-- Every finite-depth dyadic support radius is strictly below eight. -/
theorem dyadicSupportRadiusLtEight (m : ℕ) :
    8 * (1 - (1 / 2 : ℚ) ^ m) < 8 := by
  have hp : 0 < (1 / 2 : ℚ) ^ m := pow_pos (by norm_num) m
  linarith

/--
Exact centered order-sixteen spline arithmetic for `||κ||₂²`, where
`κ = b₁^{*8}`.  The analytic identification with the spline norm is outside
this finite file.
-/
theorem kappaNormSqArithmetic :
    ((16 : ℚ) ^ 15
      - 16 * 14 ^ 15
      + 120 * 12 ^ 15
      - 560 * 10 ^ 15
      + 1820 * 8 ^ 15
      - 4368 * 6 ^ 15
      + 8008 * 4 ^ 15
      - 11440 * 2 ^ 15)
      / (2 ^ 16 * Nat.factorial 15)
      = 233487 / 524288 := by
  norm_num

/-- Exact centered-spline arithmetic for `||κ'||₂² = -B₁₆''(0)`. -/
theorem kappaPrimeNormSqArithmetic :
    -(((16 : ℚ) ^ 13
      - 16 * 14 ^ 13
      + 120 * 12 ^ 13
      - 560 * 10 ^ 13
      + 1820 * 8 ^ 13
      - 4368 * 6 ^ 13
      + 8008 * 4 ^ 13
      - 11440 * 2 ^ 13)
      / (2 ^ 16 * Nat.factorial 13))
      = 5725 / 32768 := by
  norm_num

/-- Exact centered-spline arithmetic for `||κ''||₂² = B₁₆''''(0)`. -/
theorem kappaSecondNormSqArithmetic :
    ((16 : ℚ) ^ 11
      - 16 * 14 ^ 11
      + 120 * 12 ^ 11
      - 560 * 10 ^ 11
      + 1820 * 8 ^ 11
      - 4368 * 6 ^ 11
      + 8008 * 4 ^ 11
      - 11440 * 2 ^ 11)
      / (2 ^ 16 * Nat.factorial 11)
      = 35 / 128 := by
  norm_num

/-- The cross and low-order coefficients in the exact `||q_h||₂²` scaling. -/
theorem qNormCoefficientArithmetic :
    (1 / 2 : ℚ) * (5725 / 32768) = 5725 / 65536 ∧
    (1 / 16 : ℚ) * (233487 / 524288) = 233487 / 8388608 := by
  norm_num

/-- Algebraic form of the width debt hidden by a fixed-width `O_h(1)`. -/
theorem logarithmicWidthDebtAlgebra
    (c logN logh : ℝ) :
    c * logN - c * (logN + logh) = -c * logh := by
  ring

/-- Scalar exponent accounting for a width loss `A * alpha`. -/
theorem widthLossDepthBudget
    (theta gamma A alpha : ℝ)
    (hbudget : 2 * theta ≤ gamma + A * alpha) :
    theta ≤ (gamma + A * alpha) / 2 := by
  linarith

/-- Scalar exponent accounting for stable inversion of a difference. -/
theorem stableDifferenceDepthBudget
    (theta gamma beta alpha : ℝ)
    (hbudget : 2 * theta ≤ gamma + (2 - beta) * alpha) :
    theta ≤ (gamma + (2 - beta) * alpha) / 2 := by
  linarith

#print axioms binomialEightMass
#print axioms dyadicGeometricSum
#print axioms dyadicSupportRadius
#print axioms dyadicSupportRadiusLtEight
#print axioms kappaNormSqArithmetic
#print axioms kappaPrimeNormSqArithmetic
#print axioms kappaSecondNormSqArithmetic
#print axioms qNormCoefficientArithmetic
#print axioms logarithmicWidthDebtAlgebra
#print axioms widthLossDepthBudget
#print axioms stableDifferenceDepthBudget

end RHDyadicTransferFinite
end MillenniumBraid
