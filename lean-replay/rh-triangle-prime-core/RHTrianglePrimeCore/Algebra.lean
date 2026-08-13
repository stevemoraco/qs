import Mathlib

/-!
# Finite algebra for the triangular Weil prime-discrepancy criterion

This file formalizes only polynomial and scalar landing identities. It does not
formalize the Weil explicit formula, Stieltjes integration, the prime number
theorem, the archimedean infinite series, or the Riemann hypothesis.
-/

namespace Millennium.RH.TrianglePrimeCore

/-- First cubic piece of the tent autocorrelation. -/
def cLeft (u : ℝ) : ℝ := 2 / 3 - u ^ 2 + u ^ 3 / 2

/-- Second cubic piece of the tent autocorrelation. -/
def cRight (u : ℝ) : ℝ := (2 - u) ^ 3 / 6

/-- First piece of the positive derivative kernel `-C'`. -/
def kLeft (u : ℝ) : ℝ := 2 * u - 3 * u ^ 2 / 2

/-- Second piece of the positive derivative kernel `-C'`. -/
def kRight (u : ℝ) : ℝ := (2 - u) ^ 2 / 2

/-- The two autocorrelation cubics agree at their splice point. -/
theorem autocorrelation_value_match : cLeft 1 = cRight 1 := by
  norm_num [cLeft, cRight]

/-- Their formal derivative polynomials agree at the splice point. -/
theorem autocorrelation_slope_match :
    (-2 * (1 : ℝ) + 3 * (1 : ℝ) ^ 2 / 2) =
      (-(2 - (1 : ℝ)) ^ 2 / 2) := by
  norm_num

/-- The left prime-hinge cubic is exactly `-3` times the left autocorrelation. -/
theorem prime_hinge_left (u : ℝ) :
    (4 * (1 - u) ^ 3 - (2 - u) ^ 3) / 2 = -3 * cLeft u := by
  dsimp [cLeft]
  ring

/-- The right prime-hinge cubic is exactly `-3` times the right autocorrelation. -/
theorem prime_hinge_right (u : ℝ) :
    -(2 - u) ^ 3 / 2 = -3 * cRight u := by
  dsimp [cRight]
  ring

/-- The left positive kernel is the negative formal derivative of the left cubic. -/
theorem kernel_left_derivative_identity (u : ℝ) :
    kLeft u = -(-2 * u + 3 * u ^ 2 / 2) := by
  dsimp [kLeft]
  ring

/-- The right positive kernel is the negative formal derivative of the right cubic. -/
theorem kernel_right_derivative_identity (u : ℝ) :
    kRight u = -(-(2 - u) ^ 2 / 2) := by
  dsimp [kRight]
  ring

/-- The left kernel is nonnegative on `[0,1]`. -/
theorem kernel_left_nonneg (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ kLeft u := by
  have hfactor : kLeft u = u * (2 - 3 * u / 2) := by
    dsimp [kLeft]
    ring
  rw [hfactor]
  have hsecond : 0 ≤ 2 - 3 * u / 2 := by
    linarith
  positivity

/-- The right kernel is nonnegative everywhere. -/
theorem kernel_right_nonneg (u : ℝ) : 0 ≤ kRight u := by
  dsimp [kRight]
  positivity

/-- Algebraic antiderivative for the left kernel. -/
def kLeftPrimitive (u : ℝ) : ℝ := u ^ 2 - u ^ 3 / 2

/-- Algebraic antiderivative for the right kernel. -/
def kRightPrimitive (u : ℝ) : ℝ := -(2 - u) ^ 3 / 6

/-- The two kernel pieces have total mass `2/3` on `[0,2]`. -/
theorem kernel_total_mass_algebra :
    (kLeftPrimitive 1 - kLeftPrimitive 0) +
      (kRightPrimitive 2 - kRightPrimitive 1) = (2 / 3 : ℝ) := by
  norm_num [kLeftPrimitive, kRightPrimitive]

/-- Algebra behind `f'(x)=2(1-exp(-x))^2` after setting `y=exp(-x)`. -/
theorem residual_derivative_square (y : ℝ) :
    -4 * y + 2 * y ^ 2 + 2 = 2 * (1 - y) ^ 2 := by
  ring

/-- The exact scalar landing from the discrepancy average to Rayleigh sign. -/
theorem rayleigh_nonneg_iff_average_le
    (R B A : ℝ) (hR : R = B - 2 * A) :
    0 ≤ R ↔ A ≤ B / 2 := by
  rw [hR]
  constructor <;> intro h <;> linarith

/-- A bound on the Rayleigh scalar gives the corresponding half-sized error
    around the archimedean baseline average. -/
theorem average_error_of_rayleigh_bound
    (R B A delta : ℝ)
    (hR : R = B - 2 * A)
    (hbound : |R| ≤ delta) :
    |A - B / 2| ≤ delta / 2 := by
  have hident : A - B / 2 = -R / 2 := by
    linarith
  rw [hident, abs_div, abs_neg]
  gcongr

end Millennium.RH.TrianglePrimeCore
