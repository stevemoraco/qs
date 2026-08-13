import Mathlib

/-!
# Navier--Stokes axis-source scaling firewalls

This file formalizes only scalar exponent and norm-scaling identities behind a
source audit. It does not formalize cylindrical coordinates, lifted measures,
PDEs, De Giorgi iteration, or Navier--Stokes.
-/

namespace MillenniumBraid
namespace B2Round42NSAxisScaling

/-- In a source-diffusion equation with `G` exponent `a` and source-field
exponent `b`, invariance requires `a+2 = 2b+1`. -/
def equationInvariant (a b : ℝ) : Prop :=
  a + 2 = 2 * b + 1

/-- At the lifted-vorticity exponent `a=3`, equation invariance uniquely forces
source exponent `b=2`. -/
theorem sourceExponent_unique
    {b : ℝ} (h : equationInvariant 3 b) :
    b = 2 := by
  unfold equationInvariant at h
  linarith

/-- The exponent `b=3/2` fails the equation-invariance condition by one power. -/
theorem sourceExponent_threeHalves_fails :
    ¬ equationInvariant 3 ((3 : ℝ) / 2) := by
  norm_num [equationInvariant]

/-- Exact one-power mismatch in the source term at the proposed exponent. -/
theorem sourceExponent_mismatch_exact :
    (3 : ℝ) + 2 - (2 * ((3 : ℝ) / 2) + 1) = 1 := by
  norm_num

/-- Homogeneity of the fourth-power source integral in five spatial dimensions
and one parabolic time direction. -/
def sourceIntegralExponent (b : ℝ) : ℝ := 4 * b - 7

/-- The proposed exponent `3/2` makes the normalized unit-cylinder integral
scale with exponent `-1`. -/
theorem proposed_integral_exponent :
    sourceIntegralExponent ((3 : ℝ) / 2) = -1 := by
  norm_num [sourceIntegralExponent]

/-- The equation-preserving physical exponent `2` gives integral exponent `1`. -/
theorem physical_integral_exponent :
    sourceIntegralExponent 2 = 1 := by
  norm_num [sourceIntegralExponent]

/-- The paper's radius exponent `-2` differs from the physical invariant radius
exponent `+1` by three powers. -/
theorem source_norm_radius_exponent_gap :
    (1 : ℝ) - (-2) = 3 := by
  norm_num

/-- Scalar model of the manuscript source norm `R^{-2} J`. -/
noncomputable def inverseSquareSourceNorm (R J : ℝ) : ℝ := J / R ^ 2

/-- Scalar model of the physically invariant source norm `R J`. -/
def physicalSourceNorm (R J : ℝ) : ℝ := R * J

/-- Under physical forward scaling `R -> R/lambda`, `J -> lambda*J`, the
inverse-square source norm gains `lambda^3`. -/
theorem inverseSquareSourceNorm_scales_cubically
    {R λ J : ℝ} (hR : R ≠ 0) (hλ : λ ≠ 0) :
    inverseSquareSourceNorm (R / λ) (λ * J)
      = λ ^ 3 * inverseSquareSourceNorm R J := by
  unfold inverseSquareSourceNorm
  field_simp [hR, hλ]
  ring

/-- Under the same physical scaling, the radius-weighted source norm is
invariant. -/
theorem physicalSourceNorm_is_invariant
    {R λ J : ℝ} (hλ : λ ≠ 0) :
    physicalSourceNorm (R / λ) (λ * J)
      = physicalSourceNorm R J := by
  unfold physicalSourceNorm
  field_simp [hλ]
  ring

/-- At scale factor two, the manuscript source norm is multiplied by eight. -/
theorem inverseSquareSourceNorm_scale_two
    {R J : ℝ} (hR : R ≠ 0) :
    inverseSquareSourceNorm (R / 2) (2 * J)
      = 8 * inverseSquareSourceNorm R J := by
  have h := inverseSquareSourceNorm_scales_cubically
    (R := R) (λ := (2 : ℝ)) (J := J) hR (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms sourceExponent_unique
#print axioms sourceExponent_threeHalves_fails
#print axioms sourceExponent_mismatch_exact
#print axioms proposed_integral_exponent
#print axioms physical_integral_exponent
#print axioms source_norm_radius_exponent_gap
#print axioms inverseSquareSourceNorm_scales_cubically
#print axioms physicalSourceNorm_is_invariant
#print axioms inverseSquareSourceNorm_scale_two

end B2Round42NSAxisScaling
end MillenniumBraid
