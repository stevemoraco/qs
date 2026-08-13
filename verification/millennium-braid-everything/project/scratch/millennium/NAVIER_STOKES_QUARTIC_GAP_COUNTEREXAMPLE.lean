import Mathlib

/-!
# Finite counterexample to a quadratic error-bound inference

This file isolates the elementary obstruction used in the audit of
arXiv:2605.01873v2.  It does **not** prove or disprove Navier--Stokes.

The analytic paper needs a bound of the form `dist(x,Z)^2 ≤ C * defect(x)`.
Compactness, continuity and an exact zero set do not imply such a quadratic
rate.  The scalar defect `defect(x)=x^4` with `Z={0}` is the minimal counterexample.
-/

namespace NavierStokesGapAudit

/-- For `d(x)=x^4`, no nonnegative constant `C` can dominate `x^2` by
`C*d(x)` for every real `x`. -/
theorem quartic_defect_not_quadratically_coercive :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ^ 2 ≤ C * x ^ 4 := by
  rintro ⟨C, hC, hbound⟩
  have hpos : 0 < C + 1 := by linarith
  have hne : C + 1 ≠ 0 := ne_of_gt hpos
  have hx := hbound (1 / (C + 1))
  have hfac : 0 ≤ (C + 1) ^ 4 := by positivity
  have hm := mul_le_mul_of_nonneg_right hx hfac
  have hl : (1 / (C + 1)) ^ 2 * (C + 1) ^ 4 = (C + 1) ^ 2 := by
    field_simp [hne]
    <;> ring
  have hr : (C * (1 / (C + 1)) ^ 4) * (C + 1) ^ 4 = C := by
    field_simp [hne]
    <;> ring
  rw [hl, hr] at hm
  nlinarith [sq_nonneg C]

/-- Pointwise form: for every candidate constant `C ≥ 0`, there is an explicit
nonzero point where the quadratic bound fails. -/
theorem exists_violation_for_every_constant (C : ℝ) (hC : 0 ≤ C) :
    ∃ x : ℝ, x ≠ 0 ∧ C * x ^ 4 < x ^ 2 := by
  refine ⟨1 / (C + 1), ?_, ?_⟩
  · have hpos : 0 < C + 1 := by linarith
    exact one_div_ne_zero (ne_of_gt hpos)
  · have hpos : 0 < C + 1 := by linarith
    have hne : C + 1 ≠ 0 := ne_of_gt hpos
    have hfac : 0 < (C + 1) ^ 4 := by positivity
    apply (mul_lt_mul_right hfac).mp
    have hl : (C * (1 / (C + 1)) ^ 4) * (C + 1) ^ 4 = C := by
      field_simp [hne]
      <;> ring
    have hr : (1 / (C + 1)) ^ 2 * (C + 1) ^ 4 = (C + 1) ^ 2 := by
      field_simp [hne]
      <;> ring
    rw [hl, hr]
    nlinarith [sq_nonneg C]

end NavierStokesGapAudit
