import Mathlib

/-!
Finite algebra for the ideal equal-input heterochiral three-mode system.

This file proves only the radical identities and the energy-fraction consequence
of the zero-value branch relation. It does not formalize helical Fourier modes,
the Waleffe coefficient formula, Navier--Stokes evolution, localization, or any
regularity conclusion.
-/

namespace SixLaneAudit.NSHeterochiralFraction

private lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  norm_num

private lemma sqrt_two_pos : 0 < Real.sqrt 2 := by
  positivity

/-- The two off-diagonal coefficients in the linear seed/child subsystem have
positive product. -/
theorem coefficient_product_positive :
    0 < (Real.sqrt 2 - 1) * 2 := by
  have hs := sqrt_two_sq
  have hp := sqrt_two_pos
  nlinarith

/-- The three coefficient magnitudes satisfy the energy-conservation relation. -/
theorem coefficient_sum_identity :
    Real.sqrt 2 + 1 = (Real.sqrt 2 - 1) + 2 := by
  ring

/-- The radical form of the ideal high-child fraction. -/
theorem fraction_constant_identity :
    2 / (Real.sqrt 2 + 1) = 2 * (Real.sqrt 2 - 1) := by
  have hs := sqrt_two_sq
  have hden : Real.sqrt 2 + 1 ≠ 0 := by
    positivity
  field_simp [hden]
  nlinarith

/-- The ideal fraction is strictly larger than inverse square root of two. -/
theorem fraction_above_inverse_sqrt_two :
    1 / Real.sqrt 2 < 2 * (Real.sqrt 2 - 1) := by
  have hs := sqrt_two_sq
  have hp := sqrt_two_pos
  apply (div_lt_iff₀ hp).2
  nlinarith

/-- The zero-value branch relation and transferred-energy definition imply the
exact cross-multiplied fraction identity. -/
theorem branch_fraction_cross
    {y z E : ℝ}
    (hbranch : 2 * y ^ 2 = (Real.sqrt 2 - 1) * z ^ 2)
    (hE : E = y ^ 2 + z ^ 2) :
    (Real.sqrt 2 + 1) * z ^ 2 = 2 * E := by
  nlinarith

/-- On a nonzero transferred-energy state, the high-mode energy fraction has
the exact value `2 * (sqrt 2 - 1)`. -/
theorem branch_fraction_value
    {y z E : ℝ}
    (hbranch : 2 * y ^ 2 = (Real.sqrt 2 - 1) * z ^ 2)
    (hE : E = y ^ 2 + z ^ 2)
    (hEpos : 0 < E) :
    z ^ 2 / E = 2 * (Real.sqrt 2 - 1) := by
  have hcross := branch_fraction_cross hbranch hE
  have hEne : E ≠ 0 := ne_of_gt hEpos
  have hden : Real.sqrt 2 + 1 ≠ 0 := by
    positivity
  have hquot : z ^ 2 / E = 2 / (Real.sqrt 2 + 1) := by
    field_simp [hEne, hden]
    nlinarith
  rw [hquot, fraction_constant_identity]

/-- Consequently, the ideal high-mode fraction exceeds the inverse-frequency
threshold `1 / sqrt 2`. -/
theorem branch_fraction_above_threshold
    {y z E : ℝ}
    (hbranch : 2 * y ^ 2 = (Real.sqrt 2 - 1) * z ^ 2)
    (hE : E = y ^ 2 + z ^ 2)
    (hEpos : 0 < E) :
    1 / Real.sqrt 2 < z ^ 2 / E := by
  rw [branch_fraction_value hbranch hE hEpos]
  exact fraction_above_inverse_sqrt_two

#print axioms coefficient_product_positive
#print axioms coefficient_sum_identity
#print axioms fraction_constant_identity
#print axioms fraction_above_inverse_sqrt_two
#print axioms branch_fraction_cross
#print axioms branch_fraction_value
#print axioms branch_fraction_above_threshold

end SixLaneAudit.NSHeterochiralFraction
