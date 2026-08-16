import Mathlib

/-!
# B212 centered circular jump defect — finite core

Finite real algebra only.

For a centered circular Xi scan with even coordinate `u = (t / R)^2`, group
one simultaneous crossing into positive orbit weights `W_i` and real coordinate
parts `x_i`.  The first three jump moments have the scalar ledger

`j₀ = W`, `j₁ = S₁`, `j₂ = 2 S₂ - W`.

This file formalizes the resulting determinant defect, its nonnegativity on
`0 ≤ x_i ≤ 1`, an explicit negative quadratic-form witness when the defect is
positive, and the single-orbit displacement identity.

The source does **not** formalize Xi, zeta zeros, contour moments,
Deng--Yang--Lu, Platt--Trudgian, B46, RH, or not-RH.
-/

open scoped BigOperators

namespace RHB212CenteredJumpDefectFinite

/-- `j₁² - j₀ j₂` after writing `j₀=W`, `j₁=S₁`, `j₂=2S₂-W`. -/
def jumpDefect (W S₁ S₂ : ℝ) : ℝ :=
  S₁ ^ 2 - W * (2 * S₂ - W)

/-- Quadratic form of the corresponding symmetric `2 × 2` jump matrix. -/
def jumpQform (W S₁ S₂ x y : ℝ) : ℝ :=
  W * x ^ 2 + 2 * S₁ * x * y + (2 * S₂ - W) * y ^ 2

/-- Exact simultaneous-crossing defect decomposition. -/
theorem jump_defect_decomposition (W S₁ S₂ : ℝ) :
    jumpDefect W S₁ S₂ =
      (W - S₁) ^ 2 + 2 * W * (S₁ - S₂) := by
  unfold jumpDefect
  ring

/-- Nonnegative total weight and nonnegative first-minus-second real moment
force a nonnegative determinant defect. -/
theorem jump_defect_nonnegative
    {W S₁ S₂ : ℝ}
    (hW : 0 ≤ W)
    (hgap : 0 ≤ S₁ - S₂) :
    0 ≤ jumpDefect W S₁ S₂ := by
  rw [jump_defect_decomposition]
  have hprod : 0 ≤ W * (S₁ - S₂) := mul_nonneg hW hgap
  nlinarith [sq_nonneg (W - S₁)]

/-- Weighted orbit data with `0 ≤ x_i ≤ 1` satisfy the B212 defect sign. -/
theorem weighted_cluster_defect_nonnegative
    {ι : Type*}
    (s : Finset ι)
    (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) :
    0 ≤ jumpDefect
      (∑ i ∈ s, w i)
      (∑ i ∈ s, w i * x i)
      (∑ i ∈ s, w i * (x i) ^ 2) := by
  apply jump_defect_nonnegative
  · exact Finset.sum_nonneg fun i hi => hw i hi
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro i hi
    have hterm : 0 ≤ w i * x i * (1 - x i) :=
      mul_nonneg (mul_nonneg (hw i hi) (hx0 i hi))
        (sub_nonneg.mpr (hx1 i hi))
    nlinarith

/-- The jump determinant is the negative of the B212 defect. -/
theorem jump_determinant_eq_neg_defect (W S₁ S₂ : ℝ) :
    W * (2 * S₂ - W) - S₁ ^ 2 = -jumpDefect W S₁ S₂ := by
  unfold jumpDefect
  ring

/-- Explicit vector identity: `(S₁,-W)` has quadratic value `-W·defect`. -/
theorem negative_witness_identity (W S₁ S₂ : ℝ) :
    jumpQform W S₁ S₂ S₁ (-W) =
      -W * jumpDefect W S₁ S₂ := by
  unfold jumpQform jumpDefect
  ring

/-- A positive defect and positive total crossing weight give an explicit
negative direction of the `2 × 2` jump form. -/
theorem negative_witness_of_positive_defect
    {W S₁ S₂ : ℝ}
    (hW : 0 < W)
    (hD : 0 < jumpDefect W S₁ S₂) :
    jumpQform W S₁ S₂ S₁ (-W) < 0 := by
  rw [negative_witness_identity]
  exact neg_neg_of_pos (mul_pos hW hD)

/-- If every crossing coordinate equals one, the jump form is a rank-one
positive square. -/
theorem real_crossing_qform_identity (W x y : ℝ) :
    jumpQform W W W x y = W * (x + y) ^ 2 := by
  unfold jumpQform
  ring

/-- Positive total multiplicity makes the all-real crossing form PSD. -/
theorem real_crossing_qform_nonnegative
    {W x y : ℝ}
    (hW : 0 ≤ W) :
    0 ≤ jumpQform W W W x y := by
  rw [real_crossing_qform_identity]
  exact mul_nonneg hW (sq_nonneg (x + y))

/-- Exact one-orbit defect: total weight `W` at conjugate real part `x`. -/
theorem single_orbit_defect (W x : ℝ) :
    jumpDefect W (W * x) (W * x ^ 2) =
      W ^ 2 * (1 - x ^ 2) := by
  unfold jumpDefect
  ring

/-- A positive-weight orbit with `0 ≤ x < 1` creates a strictly positive defect. -/
theorem single_orbit_defect_positive
    {W x : ℝ}
    (hW : 0 < W)
    (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    0 < jumpDefect W (W * x) (W * x ^ 2) := by
  rw [single_orbit_defect]
  have hleft : 0 < 1 - x := sub_pos.mpr hx1
  have hright : 0 < 1 + x := by linarith
  have hunit : 0 < 1 - x ^ 2 := by
    have hfac : 0 < (1 - x) * (1 + x) := mul_pos hleft hright
    nlinarith
  exact mul_pos (sq_pos_of_pos hW) hunit

/-- Algebra behind the single-quartet displacement formula. -/
theorem square_coordinate_displacement (γ δ : ℝ) :
    (γ ^ 2 + δ ^ 2) ^ 2 - (γ ^ 2 - δ ^ 2) ^ 2 =
      4 * γ ^ 2 * δ ^ 2 := by
  ring

/-- The real part `(γ²-δ²)/(γ²+δ²)` is nonnegative when `δ²≤γ²`. -/
theorem square_coordinate_realpart_nonnegative
    {γ δ : ℝ}
    (hden : 0 < γ ^ 2 + δ ^ 2)
    (hdom : δ ^ 2 ≤ γ ^ 2) :
    0 ≤ (γ ^ 2 - δ ^ 2) / (γ ^ 2 + δ ^ 2) := by
  exact div_nonneg (sub_nonneg.mpr hdom) hden.le

/-- A genuinely off-line displacement gives real part strictly below one. -/
theorem square_coordinate_realpart_lt_one
    {γ δ : ℝ}
    (hden : 0 < γ ^ 2 + δ ^ 2)
    (hδ : δ ≠ 0) :
    (γ ^ 2 - δ ^ 2) / (γ ^ 2 + δ ^ 2) < 1 := by
  apply (div_lt_iff₀ hden).2
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
  nlinarith

#print axioms jump_defect_decomposition
#print axioms jump_defect_nonnegative
#print axioms weighted_cluster_defect_nonnegative
#print axioms jump_determinant_eq_neg_defect
#print axioms negative_witness_identity
#print axioms negative_witness_of_positive_defect
#print axioms real_crossing_qform_identity
#print axioms real_crossing_qform_nonnegative
#print axioms single_orbit_defect
#print axioms single_orbit_defect_positive
#print axioms square_coordinate_displacement
#print axioms square_coordinate_realpart_nonnegative
#print axioms square_coordinate_realpart_lt_one

end RHB212CenteredJumpDefectFinite
