import Mathlib

/-!
# RH unit-interval prime-endpoint trace algebra

This file formalizes the finite polynomial core of the unit-interval sampling
bridge for the dyadic Chebyshev error.

It does not formalize primes, the Chebyshev function, event-free intervals,
Lebesgue integration, the PNT, the von-Koch estimate, the B54 criterion, or RH.
-/

namespace RHUnitIntervalTrace

/-- Exact energy of the affine profile `u ↦ y + u/2` on a unit interval. -/
noncomputable def unitIntervalEnergy (y : ℝ) : ℝ :=
  y ^ 2 + y / 2 + 1 / 12

/-- Complete-square form of the unit-interval energy. -/
theorem unitIntervalEnergy_complete_square (y : ℝ) :
    unitIntervalEnergy y = (y + 1 / 4) ^ 2 + 1 / 48 := by
  unfold unitIntervalEnergy
  ring

/-- The left-limit square is controlled by twice the unit-interval energy
plus the exact constant `1/12`. -/
theorem leftLimit_sq_le_energy (y : ℝ) :
    y ^ 2 ≤ 2 * unitIntervalEnergy y + 1 / 12 := by
  unfold unitIntervalEnergy
  nlinarith [sq_nonneg (y + 1 / 2)]

/-- After a jump of size `ell`, the post-jump endpoint square is controlled by
four times the unit-interval energy plus `1/6 + 2 ell^2`. -/
theorem endpoint_sq_le_energy (y ell : ℝ) :
    (y + ell) ^ 2 ≤
      4 * unitIntervalEnergy y + 1 / 6 + 2 * ell ^ 2 := by
  have hleft := leftLimit_sq_le_energy y
  nlinarith [sq_nonneg (y - ell)]

/-- Weighted endpoint trace inequality for any nonnegative weight. -/
theorem weighted_endpoint_sq_le_energy
    {w y ell : ℝ} (hw : 0 ≤ w) :
    w * (y + ell) ^ 2 ≤
      4 * w * unitIntervalEnergy y + w / 6 + 2 * w * ell ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (endpoint_sq_le_energy y ell) hw
  nlinarith

#print axioms unitIntervalEnergy_complete_square
#print axioms leftLimit_sq_le_energy
#print axioms endpoint_sq_le_energy
#print axioms weighted_endpoint_sq_le_energy

end RHUnitIntervalTrace
