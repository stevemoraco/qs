import Mathlib

/-!
# Coplanar equal-shell pressure-selector finite core

The human proof supplies the Fourier/Leray geometry.  This file verifies only
its determinant algebra and the coordinate orthogonality of a normal
polarization to a common wavevector plane.

No PDE or Clay conclusion is present.
-/

namespace NSCoplanarPressureOutputType

/-- Visible normal coefficient at the equal-shell sum output. -/
def sumCoeff (A B C D : ℝ) : ℝ := A * D - C * B

/-- Visible normal coefficient, up to the common signed prefactor, at the
real-conjugate difference output. -/
def differenceCoeff (A B C D : ℝ) : ℝ := A * D + C * B

/-- Killing the difference coefficient makes the sum coefficient twice the
first cross product. -/
theorem kill_difference_sum_value
    {A B C D : ℝ}
    (h : differenceCoeff A B C D = 0) :
    sumCoeff A B C D = 2 * A * D := by
  unfold sumCoeff differenceCoeff at *
  linarith

/-- Killing the sum coefficient makes the difference coefficient twice the
first cross product. -/
theorem kill_sum_difference_value
    {A B C D : ℝ}
    (h : sumCoeff A B C D = 0) :
    differenceCoeff A B C D = 2 * A * D := by
  unfold sumCoeff differenceCoeff at *
  linarith

/-- Opposite normal ratios kill the `P-Q` difference channel. -/
theorem opposite_normal_ratios_kill_pair_difference (A B : ℝ) :
    differenceCoeff A B A (-B) = 0 := by
  simp [differenceCoeff]

/-- The corresponding `P+Q` sum channel remains the determinant `-2AB`. -/
theorem opposite_normal_ratios_pair_sum (A B : ℝ) :
    sumCoeff A B A (-B) = -2 * A * B := by
  simp [sumCoeff]
  ring

/-- One scalar compatibility equation selects the desired catalyst sums and
kills both opposite sidebands in the signed three-mode cell. -/
theorem catalyst_selector_compatibility
    {A B C D : ℝ}
    (h : A * D + C * B = 0) :
    differenceCoeff A B C D = 0 ∧
      differenceCoeff A (-B) (-C) D = 0 ∧
      sumCoeff A B C D = -2 * C * B ∧
      sumCoeff A (-B) (-C) D = -2 * C * B := by
  unfold sumCoeff differenceCoeff
  constructor
  · exact h
  constructor
  · simpa [mul_assoc, mul_left_comm, mul_comm] using h
  constructor <;> linarith

/-- A vector parallel to the third coordinate axis is orthogonal to every
wavevector in the first two coordinate directions. -/
theorem normal_dot_planar (a x y : ℝ) :
    0 * x + 0 * y + a * 0 = 0 := by
  ring

/-- Two normal-polarized coefficients have zero advective dot factors against
arbitrary coplanar wavevectors. -/
theorem two_normal_modes_have_zero_transport_factors
    (a b kx ky lx ly : ℝ) :
    (0 * lx + 0 * ly + a * 0 = 0) ∧
      (0 * kx + 0 * ky + b * 0 = 0) := by
  constructor <;> ring

#print axioms kill_difference_sum_value
#print axioms kill_sum_difference_value
#print axioms opposite_normal_ratios_kill_pair_difference
#print axioms opposite_normal_ratios_pair_sum
#print axioms catalyst_selector_compatibility
#print axioms normal_dot_planar
#print axioms two_normal_modes_have_zero_transport_factors

end NSCoplanarPressureOutputType
