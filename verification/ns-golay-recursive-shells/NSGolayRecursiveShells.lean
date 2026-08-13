import Mathlib

/-!
# Exact recursive integer shells: finite arithmetic core

This file formalizes only:

* the integer rational-circle identity after clearing a common denominator;
* the `3-4-5` integer carrier radius;
* the shifted partner-shell identity;
* the exact coordinatewise common difference;
* the radial-gap rationalization numerator bounds; and
* the corrected return-margin implication from a scale budget.

It does not formalize Fourier packets, helical polarization, Golay arrays,
Navier--Stokes evolution, recursive profile closure, shadowing, or blow-up.
-/

namespace NSGolayRecursiveShells

/-- BANKER: after writing `K=q(M²+j²)`, the rational-circle coordinates are
integers and lie exactly on the radius-`4K` circle. -/
theorem cleared_rational_circle_identity
    (K M j q : ℤ) (hK : K = q * (M ^ 2 + j ^ 2)) :
    (4 * q * (M ^ 2 - j ^ 2)) ^ 2 +
        (8 * q * M * j) ^ 2 = (4 * K) ^ 2 := by
  rw [hK]
  ring

/-- The latitude circle with fixed first coordinate `3K` lies on the exact
integer-radius sphere `5K`. -/
theorem pythagorean_carrier_radius
    (K Y Z : ℤ) (hcircle : Y ^ 2 + Z ^ 2 = (4 * K) ^ 2) :
    (3 * K) ^ 2 + Y ^ 2 + Z ^ 2 = (5 * K) ^ 2 := by
  nlinarith

/-- Shifting the first coordinate by a prescribed lower frequency `r`
places every partner on one common second shell. -/
theorem shifted_partner_shell_identity
    (K Y Z r : ℤ) (hcircle : Y ^ 2 + Z ^ 2 = (4 * K) ^ 2) :
    (3 * K - r) ^ 2 + Y ^ 2 + Z ^ 2 =
      25 * K ^ 2 - 6 * K * r + r ^ 2 := by
  nlinarith

/-- The carrier and its shifted partner have exactly the prescribed common
difference in every coordinate. -/
theorem exact_common_difference
    (K Y Z r : ℤ) :
    (3 * K - (3 * K - r) = r) ∧
      (Y - Y = 0) ∧ (Z - Z = 0) := by
  constructor
  · ring
  · constructor <;> ring

/-- The difference of the squared shell radii is exactly the rationalization
numerator `r(6K-r)`. -/
theorem radial_gap_numerator_identity
    (K r : ℤ) :
    (5 * K) ^ 2 - (25 * K ^ 2 - 6 * K * r + r ^ 2) =
      r * (6 * K - r) := by
  ring

/-- If `0≤r≤K`, the radial-gap numerator lies between `5Kr` and `6Kr`. -/
theorem radial_gap_numerator_bounds
    (K r : ℝ) (hr0 : 0 ≤ r) (hrK : r ≤ K) :
    5 * K * r ≤ r * (6 * K - r) ∧
      r * (6 * K - r) ≤ 6 * K * r := by
  constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hrK)]

/-- CLEANER: the exact recursive scale budget `r M⁸≤K` implies the corrected
quadratic return margin `r M²/K≤M⁻⁶`. -/
theorem scale_budget_gives_sixth_power_return_margin
    (K r M : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hr : 0 ≤ r)
    (hscale : r * M ^ 8 ≤ K) :
    r * M ^ 2 / K ≤ 1 / M ^ 6 := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hM6 : 0 < M ^ 6 := by positivity
  have hKM6 : 0 < K * M ^ 6 := mul_pos hK hM6
  apply (div_le_iff₀ hK).2
  apply (le_div_iff₀ hM6).2
  calc
    r * M ^ 2 * M ^ 6 = r * M ^ 8 := by ring
    _ ≤ K := hscale
    _ = K * 1 := by ring

#print axioms cleared_rational_circle_identity
#print axioms pythagorean_carrier_radius
#print axioms shifted_partner_shell_identity
#print axioms exact_common_difference
#print axioms radial_gap_numerator_identity
#print axioms radial_gap_numerator_bounds
#print axioms scale_budget_gives_sixth_power_return_margin

end NSGolayRecursiveShells
