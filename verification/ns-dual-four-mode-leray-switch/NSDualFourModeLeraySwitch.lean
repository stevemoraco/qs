import Mathlib

/-!
# Dual four-mode Leray switch: finite coefficient core

This file formalizes only the scalar/vector-coordinate algebra behind the
one-generation frequency switch. It does not formalize Fourier series, the
Leray projector as an operator, Navier--Stokes, forcing, an infinite cascade,
or any Clay statement.
-/

namespace NSDualFourModeLeraySwitch

/-- The first polarization is transverse to `k1=(K,n,0)`. -/
theorem a_transverse_k1 (K n : ℝ) :
    n * K + (-K) * n + K * 0 = 0 := by
  ring

/-- The switched second polarization `b=(n,K,K)` is transverse to
`k2=(-K,n,0)`. -/
theorem bPlus_transverse_k2 (K n : ℝ) :
    n * (-K) + K * n + K * 0 = 0 := by
  ring

/-- The cross contraction of `a` with `k2` is `-2Kn`. -/
theorem a_dot_k2 (K n : ℝ) :
    n * (-K) + (-K) * n + K * 0 = -2 * K * n := by
  ring

/-- The cross contraction of `bPlus` with `k1` is `2Kn`. -/
theorem bPlus_dot_k1 (K n : ℝ) :
    n * K + K * n + K * 0 = 2 * K * n := by
  ring

/-- In the switched orientation, `bPlus-a=(0,2K,0)`, hence the low
sum-frequency coefficient is parallel to `ell=(0,2n,0)`. -/
theorem low_sum_coefficient_is_axial (K n : ℝ) :
    (n - n, K - (-K), K - K) = ((0 : ℝ), 2 * K, 0) := by
  ext <;> ring

/-- In the switched orientation, `a+bPlus=(2n,0,2K)`. -/
theorem high_difference_raw_coefficient (K n : ℝ) :
    (n + n, (-K) + K, K + K) = (2 * n, (0 : ℝ), 2 * K) := by
  ext <;> ring

/-- Projecting `(2n,0,2K)` orthogonally to the x-axis removes exactly
its first coordinate and retains the vertical payload `(0,0,2K)`. -/
theorem high_difference_transverse_payload (K n : ℝ) :
    ((2 * n : ℝ) - 2 * n, (0 : ℝ), 2 * K) = (0, 0, 2 * K) := by
  ext <;> ring

/-- The surviving quadratic scalar coefficient is `-2 K^2 n`. -/
theorem high_output_coefficient (K n : ℝ) :
    -(K * n) * (2 * K) = -2 * K ^ 2 * n := by
  ring

/-- With the old sign `bMinus=(n,K,-K)`, the high-difference raw
coefficient is purely x-axial and is therefore the pressure branch. -/
theorem old_orientation_high_is_axial (K n : ℝ) :
    (n + n, (-K) + K, K + (-K)) = (2 * n, (0 : ℝ), 0) := by
  ext <;> ring

/-- With the old sign, the low coefficient retains a vertical component. -/
theorem old_orientation_low_has_vertical_payload (K n : ℝ) :
    (n - n, K - (-K), (-K) - K) = ((0 : ℝ), 2 * K, -2 * K) := by
  ext <;> ring

#print axioms a_transverse_k1
#print axioms bPlus_transverse_k2
#print axioms a_dot_k2
#print axioms bPlus_dot_k1
#print axioms low_sum_coefficient_is_axial
#print axioms high_difference_raw_coefficient
#print axioms high_difference_transverse_payload
#print axioms high_output_coefficient
#print axioms old_orientation_high_is_axial
#print axioms old_orientation_low_has_vertical_payload

end NSDualFourModeLeraySwitch
