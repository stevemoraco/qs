import Mathlib

/-!
Finite algebraic spine for the cubic shell-orbit Navier–Stokes research branch.

This file formalizes only real polynomial positivity, exact representative
coefficient norms, and shell-ratio inequalities. It does not formalize the
cubic group action, Fourier series, Leray projection, Navier–Stokes, an
infinite mode tree, or any Clay statement.
-/

namespace NSCubicShellOrbitCore

/-- Common positive-definite factor in the first cubic-shell outputs. -/
def shellFactor (A B : ℝ) : ℝ := A ^ 2 + 5 * B ^ 2

/-- A nonzero transverse seed makes the common shell factor strictly positive. -/
theorem shellFactor_pos
    {A B : ℝ}
    (h : A ≠ 0 ∨ B ≠ 0) :
    0 < shellFactor A B := by
  unfold shellFactor
  rcases h with hA | hB
  · have hs : 0 < A ^ 2 := sq_pos_of_ne_zero hA
    nlinarith [sq_nonneg B]
  · have hs : 0 < B ^ 2 := sq_pos_of_ne_zero hB
    nlinarith [sq_nonneg A]

/-- Vanishing of the common factor forces the zero polarization. -/
theorem shellFactor_eq_zero_iff (A B : ℝ) :
    shellFactor A B = 0 ↔ A = 0 ∧ B = 0 := by
  unfold shellFactor
  constructor
  · intro h
    have hA : A ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
    have hB : B ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
    exact ⟨sq_eq_zero_iff.mp hA, sq_eq_zero_iff.mp hB⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Squared norm of `(4/3) Q (1,-1,-1)`. -/
theorem shell6_norm_sq (Q : ℝ) :
    (4 * Q / 3) ^ 2 + (-4 * Q / 3) ^ 2 + (-4 * Q / 3) ^ 2
      = (16 / 3 : ℝ) * Q ^ 2 := by
  ring

/-- Squared norm of `(6/7) Q (-2,1,4)`. -/
theorem shell14_norm_sq (Q : ℝ) :
    (-12 * Q / 7) ^ 2 + (6 * Q / 7) ^ 2 + (24 * Q / 7) ^ 2
      = (108 / 7 : ℝ) * Q ^ 2 := by
  ring

/-- Squared norm of `(8/9) Q (1,-2,-2)`. -/
theorem shell18_norm_sq (Q : ℝ) :
    (8 * Q / 9) ^ 2 + (-16 * Q / 9) ^ 2 + (-16 * Q / 9) ^ 2
      = (64 / 9 : ℝ) * Q ^ 2 := by
  ring

/-- The first promoted shell ratio `sqrt(14/5)` is strictly sub-doubling at the squared level. -/
theorem shell5_to_14_subdoubling : (14 : ℚ) < 4 * 5 := by
  norm_num

/-- The next promoted shell ratio `sqrt(30/14)` is strictly sub-doubling. -/
theorem shell14_to_30_subdoubling : (30 : ℚ) < 4 * 14 := by
  norm_num

/-- The third observed promoted shell ratio `sqrt(66/30)` is strictly sub-doubling. -/
theorem shell30_to_66_subdoubling : (66 : ℚ) < 4 * 30 := by
  norm_num

#print axioms shellFactor_pos
#print axioms shellFactor_eq_zero_iff
#print axioms shell6_norm_sq
#print axioms shell14_norm_sq
#print axioms shell18_norm_sq
#print axioms shell5_to_14_subdoubling
#print axioms shell14_to_30_subdoubling
#print axioms shell30_to_66_subdoubling

end NSCubicShellOrbitCore
