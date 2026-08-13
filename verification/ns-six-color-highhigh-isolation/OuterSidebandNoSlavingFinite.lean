import Mathlib

/-!
# Outer-sideband no-slaving: finite scalar core

This file formalizes only polynomial identities and inequalities used by the
frozen activation calculation. It does not formalize the ODE solution formula,
Fourier analysis, Navier--Stokes, an infinite cascade, or blowup.
-/

namespace NSBraid
namespace OuterSidebandNoSlaving

/-- The outer and desired high squared frequencies differ by exactly eight
lower half-carrier units, independently of the color parameter. -/
theorem outer_minus_high_sq (M H2 : ℝ) :
    (9 * M + H2) - (M + H2) = 8 * M := by
  ring

/-- Desired amplifier and outer-sideband coefficients have the same absolute
magnitude in the symmetric carrier algebra. -/
theorem coefficient_magnitudes_equal (M H2 : ℝ) :
    |-(2 * M * H2)| = |2 * M * H2| := by
  rw [abs_neg]

/-- Exact relative viscous squared-frequency gap for the parametric colors. -/
theorem relative_gap_identity (C : ℝ) :
    (8 * 198) / (198 + 396 * C ^ 2) =
      8 / (1 + 2 * C ^ 2) := by
  have h₁ : 198 + 396 * C ^ 2 ≠ 0 := by positivity
  have h₂ : 1 + 2 * C ^ 2 ≠ 0 := by positivity
  field_simp [h₁, h₂]
  ring

/-- For `C >= 20`, the desired high damping is more than one hundred times
the fixed outer-minus-high damping gap, after multiplying by any nonnegative
viscosity/scale factor. -/
theorem high_damping_dominates_gap
    (C ν R : ℝ) (hC : 20 ≤ C) (hν : 0 ≤ ν) (hR : 0 ≤ R) :
    100 * (1584 * ν * R ^ 2) ≤
      (198 + 396 * C ^ 2) * ν * R ^ 2 := by
  have hC2 : 400 ≤ C ^ 2 := by nlinarith
  have hfactor : 0 ≤ ν * R ^ 2 := mul_nonneg hν (sq_nonneg R)
  have hcoeff : 100 * 1584 ≤ 198 + 396 * C ^ 2 := by
    nlinarith
  nlinarith

/-- If the raw amplifier beats the desired high damping, then at `C >= 20`
it also beats one hundred times the outer-minus-high damping gap. -/
theorem growth_implies_hundred_gap
    (A Dh δ : ℝ)
    (hdom : 100 * δ ≤ Dh)
    (hgrowth : Dh < A) :
    100 * δ < A := by
  exact lt_of_le_of_lt hdom hgrowth

/-- The algebraic prefactor in the exact sideband/high ratio is then larger
than `100/101`. -/
theorem amplifier_fraction_gt
    (A δ : ℝ) (hδ : 0 ≤ δ) (hA : 100 * δ < A) :
    (100 / 101 : ℝ) < A / (A + δ) := by
  have hApos : 0 < A := by nlinarith
  have hden : 0 < A + δ := by linarith
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 101) hden]
  nlinarith

/-- Combining a prefactor above `100/101` with any activation bracket above
`1/2` puts the sideband above `50/101` of the desired high amplitude. -/
theorem sideband_fraction_gt
    (prefactor bracket : ℝ)
    (hpref : (100 / 101 : ℝ) < prefactor)
    (hbracket : (1 / 2 : ℝ) < bracket) :
    (50 / 101 : ℝ) < prefactor * bracket := by
  have hprod :
      0 < (prefactor - 100 / 101) * (bracket - 1 / 2) :=
    mul_pos (sub_pos.mpr hpref) (sub_pos.mpr hbracket)
  nlinarith

/-- The elementary constant comparison used in the prose lower bound. -/
theorem fifty_over_one_oh_one_gt_point_four_nine_five :
    (495 / 1000 : ℝ) < 50 / 101 := by
  norm_num

#print axioms outer_minus_high_sq
#print axioms coefficient_magnitudes_equal
#print axioms relative_gap_identity
#print axioms high_damping_dominates_gap
#print axioms growth_implies_hundred_gap
#print axioms amplifier_fraction_gt
#print axioms sideband_fraction_gt
#print axioms fifty_over_one_oh_one_gt_point_four_nine_five

end OuterSidebandNoSlaving
end NSBraid
