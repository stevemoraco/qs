import Mathlib

/-!
# Navier--Stokes critical-score scaling firewall

This file formalizes only scalar homogeneity identities. It does not formalize
Navier--Stokes solutions, vorticity, balls, integrals, or continuation.
-/

namespace MillenniumBraid
namespace B2Round42NSScaling

/-- Scalar shadow of the manuscript score `rho^{-1} * I`. -/
noncomputable def inverseRadiusScore (ρ I : ℝ) : ℝ := I / ρ

/-- Scalar shadow of the scale-invariant spatial vorticity score `rho * I`. -/
def radiusScore (ρ I : ℝ) : ℝ := ρ * I

/-- If radius changes by `rho -> rho/lambda` and the spatial vorticity integral
changes by `I -> lambda*I`, the inverse-radius score gains `lambda^2`. -/
theorem inverseRadiusScore_scales_quadratically
    {ρ λ I : ℝ} (hρ : ρ ≠ 0) (hλ : λ ≠ 0) :
    inverseRadiusScore (ρ / λ) (λ * I)
      = λ ^ 2 * inverseRadiusScore ρ I := by
  unfold inverseRadiusScore
  field_simp [hρ, hλ]
  ring

/-- Under the same scaling, the radius-weighted spatial score is invariant. -/
theorem radiusScore_is_invariant
    {ρ λ I : ℝ} (hλ : λ ≠ 0) :
    radiusScore (ρ / λ) (λ * I) = radiusScore ρ I := by
  unfold radiusScore
  field_simp [hλ]
  ring

/-- At the explicit scale factor two, the inverse-radius score is multiplied by
four. -/
theorem inverseRadiusScore_scale_two
    {ρ I : ℝ} (hρ : ρ ≠ 0) :
    inverseRadiusScore (ρ / 2) (2 * I)
      = 4 * inverseRadiusScore ρ I := by
  have h := inverseRadiusScore_scales_quadratically
    (ρ := ρ) (λ := (2 : ℝ)) (I := I) hρ (by norm_num)
  norm_num at h ⊢
  exact h

/-- A nonzero score cannot be invariant under scale factor two. -/
theorem inverseRadiusScore_not_invariant_at_two
    {ρ I : ℝ} (hρ : ρ ≠ 0)
    (hscore : inverseRadiusScore ρ I ≠ 0) :
    inverseRadiusScore (ρ / 2) (2 * I)
      ≠ inverseRadiusScore ρ I := by
  rw [inverseRadiusScore_scale_two hρ]
  intro h
  apply hscore
  linarith

/-- Scalar shadow of the spacetime scaling: if a spacetime integral changes as
`J -> J/lambda`, the inverse-radius spacetime score is invariant. -/
theorem inverseRadius_spacetime_is_invariant
    {ρ λ J : ℝ} (hρ : ρ ≠ 0) (hλ : λ ≠ 0) :
    inverseRadiusScore (ρ / λ) (J / λ)
      = inverseRadiusScore ρ J := by
  unfold inverseRadiusScore
  field_simp [hρ, hλ]
  ring

#print axioms inverseRadiusScore_scales_quadratically
#print axioms radiusScore_is_invariant
#print axioms inverseRadiusScore_scale_two
#print axioms inverseRadiusScore_not_invariant_at_two
#print axioms inverseRadius_spacetime_is_invariant

end B2Round42NSScaling
end MillenniumBraid
