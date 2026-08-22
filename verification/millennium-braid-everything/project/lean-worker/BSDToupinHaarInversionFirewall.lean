import Mathlib

namespace BSDToupinHaarInversionFirewall

noncomputable section

/-!
# Scalar density firewall for the claimed `GL₂` Haar inversion law

For determinant magnitude `d>0`, the real `GL₂` Haar density relative to
Euclidean matrix-entry measure is `d⁻²`.  Matrix inversion has Euclidean
Jacobian `d⁻⁴`, while the Haar density evaluated at the inverse is `d²`.
Their product is again `d⁻²`, not `d⁻⁴`.

This file verifies the finite exponent arithmetic, including the diagnostic
`d=2`.  It does not formalize Haar measure or prove BSD.
-/

/-- Original `GL₂` Haar density as a function of determinant magnitude. -/
def haarDensity (d : ℝ) : ℝ := d⁻¹ ^ 2

/-- Euclidean Jacobian magnitude of inversion on four matrix coordinates. -/
def inversionJacobian (d : ℝ) : ℝ := d⁻¹ ^ 4

/-- Haar density evaluated at the inverse point. -/
def inversePointDensity (d : ℝ) : ℝ := d ^ 2

/-- The correctly transformed density. -/
def transformedDensity (d : ℝ) : ℝ :=
  inversePointDensity d * inversionJacobian d

/-- The paper's extra-weight expression. -/
def claimedWeightedDensity (d : ℝ) : ℝ :=
  haarDensity d * haarDensity d

/-- Abstract exponent identity: inverse-point density `d²` cancels half of the
four-coordinate Jacobian `d⁻⁴`, leaving the original `d⁻²` density. -/
theorem exponent_cancellation
    {d : ℝ} (hd : d ≠ 0) :
    d ^ 2 * d⁻¹ ^ 4 = d⁻¹ ^ 2 := by
  field_simp [hd]

/-- For nonzero determinant magnitude, inversion preserves the Haar density. -/
theorem transformedDensity_eq_haarDensity
    {d : ℝ} (hd : d ≠ 0) :
    transformedDensity d = haarDensity d := by
  simpa [transformedDensity, inversePointDensity,
    inversionJacobian, haarDensity] using exponent_cancellation hd

/-- Exact determinant-two diagnostic: original and transformed density are
`1/4`. -/
theorem determinant_two_correct_density :
    haarDensity 2 = (1 : ℝ) / 4 ∧
      transformedDensity 2 = (1 : ℝ) / 4 := by
  constructor <;>
    norm_num [haarDensity, transformedDensity,
      inversePointDensity, inversionJacobian]

/-- The claimed extra-weight density is instead `1/16` at determinant two. -/
theorem determinant_two_claimed_density :
    claimedWeightedDensity 2 = (1 : ℝ) / 16 := by
  norm_num [claimedWeightedDensity, haarDensity]

/-- Therefore the claimed weighted inversion density disagrees with the correct
change-of-variables density. -/
theorem claimed_inversion_weight_fails_at_determinant_two :
    transformedDensity 2 ≠ claimedWeightedDensity 2 := by
  norm_num [transformedDensity, inversePointDensity,
    inversionJacobian, claimedWeightedDensity, haarDensity]

#print axioms transformedDensity_eq_haarDensity
#print axioms determinant_two_correct_density
#print axioms determinant_two_claimed_density
#print axioms claimed_inversion_weight_fails_at_determinant_two
#print axioms exponent_cancellation

end

end BSDToupinHaarInversionFirewall
