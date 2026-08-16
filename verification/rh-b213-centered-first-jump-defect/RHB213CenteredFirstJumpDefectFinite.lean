import Mathlib

/-!
# B213 centered first-jump defect — finite core

Finite real algebra only.

For positive crossing-orbit weights `w_i` and centered square-coordinate real
parts `x_i ≤ 1`, the zeroth-minus-first jump moment is

`Σ w_i - Σ w_i x_i = Σ w_i (1-x_i) ≥ 0`.

It vanishes only when every positive-weight orbit has `x_i=1`; one off-line
orbit has strict positive defect.  This file formalizes the scalar identities
and the single-quartet displacement formula.

The source does **not** formalize Xi, zeta zeros, contour moments,
Deng--Yang--Lu, B46, RH, or not-RH.
-/

open scoped BigOperators

namespace RHB213CenteredFirstJumpDefectFinite

/-- Zeroth-minus-first crossing moment. -/
def firstJumpDefect (W S₁ : ℝ) : ℝ := W - S₁

/-- Exact weighted-orbit expansion. -/
theorem first_jump_defect_weighted_identity
    {ι : Type*}
    (s : Finset ι)
    (w x : ι → ℝ) :
    firstJumpDefect
      (∑ i ∈ s, w i)
      (∑ i ∈ s, w i * x i) =
      ∑ i ∈ s, w i * (1 - x i) := by
  unfold firstJumpDefect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Positive weights and `x_i≤1` make the first-jump defect nonnegative. -/
theorem weighted_first_jump_defect_nonnegative
    {ι : Type*}
    (s : Finset ι)
    (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) :
    0 ≤ firstJumpDefect
      (∑ i ∈ s, w i)
      (∑ i ∈ s, w i * x i) := by
  rw [first_jump_defect_weighted_identity]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi) (sub_nonneg.mpr (hx1 i hi))

/-- One grouped orbit has defect `W(1-x)`. -/
theorem single_orbit_first_jump_defect (W x : ℝ) :
    firstJumpDefect W (W * x) = W * (1 - x) := by
  unfold firstJumpDefect
  ring

/-- A positive-weight orbit with real part strictly below one gives a strict
positive first-jump defect. -/
theorem single_orbit_first_jump_defect_positive
    {W x : ℝ}
    (hW : 0 < W)
    (hx : x < 1) :
    0 < firstJumpDefect W (W * x) := by
  rw [single_orbit_first_jump_defect]
  exact mul_pos hW (sub_pos.mpr hx)

/-- Cleared numerator identity behind
`1-(γ²-δ²)/(γ²+δ²)=2δ²/(γ²+δ²)`. -/
theorem square_coordinate_first_defect_numerator (γ δ : ℝ) :
    (γ ^ 2 + δ ^ 2) - (γ ^ 2 - δ ^ 2) = 2 * δ ^ 2 := by
  ring

/-- Exact single-quartet formula with grouped weight `4m`. -/
theorem single_quartet_first_jump_defect
    (m γ δ : ℝ)
    (hden : γ ^ 2 + δ ^ 2 ≠ 0) :
    firstJumpDefect
      (4 * m)
      (4 * m * ((γ ^ 2 - δ ^ 2) / (γ ^ 2 + δ ^ 2))) =
      8 * m * δ ^ 2 / (γ ^ 2 + δ ^ 2) := by
  unfold firstJumpDefect
  field_simp [hden]
  ring

/-- The one-dimensional scalar `S₁-W` is negative exactly when the first defect
is positive. -/
theorem negative_scalar_of_positive_first_defect
    {W S₁ : ℝ}
    (hD : 0 < firstJumpDefect W S₁) :
    S₁ - W < 0 := by
  unfold firstJumpDefect at hD
  linarith

/-- B212's determinant defect is the square of the B213 first defect plus the
remaining nonnegative moment-gap term. -/
theorem determinant_defect_refinement (W S₁ S₂ : ℝ) :
    S₁ ^ 2 - W * (2 * S₂ - W) =
      firstJumpDefect W S₁ ^ 2 + 2 * W * (S₁ - S₂) := by
  unfold firstJumpDefect
  ring

#print axioms first_jump_defect_weighted_identity
#print axioms weighted_first_jump_defect_nonnegative
#print axioms single_orbit_first_jump_defect
#print axioms single_orbit_first_jump_defect_positive
#print axioms square_coordinate_first_defect_numerator
#print axioms single_quartet_first_jump_defect
#print axioms negative_scalar_of_positive_first_defect
#print axioms determinant_defect_refinement

end RHB213CenteredFirstJumpDefectFinite
