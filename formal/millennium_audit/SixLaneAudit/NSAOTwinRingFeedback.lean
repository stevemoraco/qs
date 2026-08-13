import Mathlib

namespace NSAOTwinRingFeedback

/-- The intensity-normalized factor in the leading AO `Λ` feedback,
with `t = κ ξ²`. -/
def shapeFactor (t : ℝ) : ℝ := 1 - 2 * t

/-- The nontrivial factor in the derivative of the feedback profile. -/
def criticalFactor (t : ℝ) : ℝ := 2 * t - 3

/-- The coefficient of `C κ exp(-t)` in the second derivative of the feedback. -/
def curvatureCoefficient (t : ℝ) : ℝ :=
  -2 * (4 * t ^ 2 - 12 * t + 3)

/-- The center has positive shape coefficient. -/
theorem shape_at_center : shapeFactor 0 = 1 := by
  norm_num [shapeFactor]

/-- The two sign-change points satisfy `κ ξ² = 1/2`. -/
theorem shape_at_zero_crossing : shapeFactor ((1 : ℝ) / 2) = 0 := by
  norm_num [shapeFactor]

/-- The two off-center critical points satisfy `κ ξ² = 3/2`. -/
theorem critical_factor_at_shoulder :
    criticalFactor ((3 : ℝ) / 2) = 0 := by
  norm_num [criticalFactor]

/-- The feedback value at either shoulder is `-2` times its positive envelope. -/
theorem shape_at_shoulder : shapeFactor ((3 : ℝ) / 2) = -2 := by
  norm_num [shapeFactor]

/-- The normalized center curvature coefficient is negative. -/
theorem curvature_at_center : curvatureCoefficient 0 = -6 := by
  norm_num [curvatureCoefficient]

/-- The normalized shoulder curvature coefficient is positive. -/
theorem curvature_at_shoulder :
    curvatureCoefficient ((3 : ℝ) / 2) = 12 := by
  norm_num [curvatureCoefficient]

/-- Positive amplitude and scale make the center curvature strictly negative. -/
theorem center_curvature_negative
    (C κ q : ℝ) (hC : 0 < C) (hκ : 0 < κ) (hq : 0 < q) :
    C * κ * curvatureCoefficient 0 * q < 0 := by
  rw [curvature_at_center]
  have hp : 0 < C * κ * q := mul_pos (mul_pos hC hκ) hq
  nlinarith

/-- Positive amplitude and scale make the shoulder curvature strictly positive. -/
theorem shoulder_curvature_positive
    (C κ q : ℝ) (hC : 0 < C) (hκ : 0 < κ) (hq : 0 < q) :
    0 < C * κ * curvatureCoefficient ((3 : ℝ) / 2) * q := by
  rw [curvature_at_shoulder]
  positivity

/-- The derivative of `Λ = β W - Γ/r²` at one radius, expressed through the
point jets of `W` and `Γ`. -/
noncomputable def lambdaDerivative (β r Γ Wp Γp : ℝ) : ℝ :=
  β * Wp - Γp / r ^ 2 + 2 * Γ / r ^ 3

/-- The AO coefficient `b` after eliminating `q` and `Φ` from the source
formulas:
`b = -2 β Γ (W' + β Γ') / [r (1 + β² r²)]`. -/
noncomputable def bReduced (β r Γ Wp Γp : ℝ) : ℝ :=
  -2 * β * Γ * (Wp + β * Γp) / (r * (1 + β ^ 2 * r ^ 2))

/-- A point-jet perturbation in the kernel of `Λ` leaves `Λ'` unchanged. -/
theorem lambda_derivative_kernel
    (β r Γ Wp Γp ε u : ℝ)
    (hβ : β ≠ 0) (hr : r ≠ 0) :
    lambdaDerivative β r Γ
        (Wp + ε * u / (β * r ^ 2)) (Γp + ε * u) =
      lambdaDerivative β r Γ Wp Γp := by
  unfold lambdaDerivative
  field_simp [hβ, hr]
  ring

/-- The same `Λ`-invisible point-jet perturbation changes `b` by an explicit
amount. This is the finite algebraic obstruction to recovering the AO child
coefficient `b` from `F_Λ` alone. -/
theorem b_changes_in_lambda_kernel
    (β r Γ Wp Γp ε u : ℝ)
    (hβ : β ≠ 0) (hr : r ≠ 0)
    (hden : 1 + β ^ 2 * r ^ 2 ≠ 0) :
    bReduced β r Γ
        (Wp + ε * u / (β * r ^ 2)) (Γp + ε * u) -
      bReduced β r Γ Wp Γp =
        -2 * ε * Γ * u / r ^ 3 := by
  unfold bReduced
  field_simp [hβ, hr, hden]
  ring

#print axioms shape_at_center
#print axioms shape_at_zero_crossing
#print axioms critical_factor_at_shoulder
#print axioms shape_at_shoulder
#print axioms curvature_at_center
#print axioms curvature_at_shoulder
#print axioms center_curvature_negative
#print axioms shoulder_curvature_positive
#print axioms lambda_derivative_kernel
#print axioms b_changes_in_lambda_kernel

end NSAOTwinRingFeedback
