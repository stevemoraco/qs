import Mathlib

/-!
# RH deletion/insertion geometry: finite scalar core

This file formalizes only abstract extension-by-zero lower-bound transfer,
positive-definiteness of a two-sector scalar quadratic form under a positive
Schur determinant, and the duplicate zero mode.

It does not formalize Hilbert-space Riesz sequences, infinite Gram operators,
Schur complements, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHInsertionSchurFinite

/-- Any lower bound valid on a full coefficient space restricts through an
extension map once that map preserves the coefficient norm. This is the abstract
extension-by-zero core of deletion invariance. -/
theorem lower_bound_restricts_through_isometric_extension
    {C D : Type*}
    (extend : D → C)
    (coeffNormSq : C → ℝ)
    (subCoeffNormSq : D → ℝ)
    (energy : C → ℝ)
    (A : ℝ)
    (hnorm : ∀ d, coeffNormSq (extend d) = subCoeffNormSq d)
    (hfull : ∀ c, A * coeffNormSq c ≤ energy c) :
    ∀ d, A * subCoeffNormSq d ≤ energy (extend d) := by
  intro d
  simpa [hnorm d] using hfull (extend d)

/-- A positive leading pivot and positive Schur determinant make the scalar
insertion quadratic form strictly positive away from the origin. -/
theorem insertion_quadratic_positive
    (A b eta x y : ℝ)
    (hA : 0 < A)
    (hdet : eta ^ 2 < A * b)
    (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < A * x ^ 2 + b * y ^ 2 - 2 * eta * x * y := by
  have hschur : 0 < A * b - eta ^ 2 := by nlinarith
  have hid :
      A * (A * x ^ 2 + b * y ^ 2 - 2 * eta * x * y) =
        (A * x - eta * y) ^ 2 + (A * b - eta ^ 2) * y ^ 2 := by
    ring
  rcases hne with hx | hy
  · by_cases hy0 : y = 0
    · subst y
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      nlinarith
    · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy0
      have hright :
          0 < (A * x - eta * y) ^ 2 + (A * b - eta ^ 2) * y ^ 2 := by
        positivity
      nlinarith
  · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hright :
        0 < (A * x - eta * y) ^ 2 + (A * b - eta ^ 2) * y ^ 2 := by
      positivity
    nlinarith

/-- The positive determinant condition automatically forces the inserted-sector
pivot to be positive. -/
theorem inserted_pivot_positive
    (A b eta : ℝ)
    (hA : 0 < A)
    (hdet : eta ^ 2 < A * b) :
    0 < b := by
  nlinarith [sq_nonneg eta]

/-- An exact duplicate produces a zero mode for opposite coefficients. -/
theorem duplicate_zero_mode :
    (1 : ℝ) * 1 ^ 2 + 1 * (-1) ^ 2 + 2 * 1 * 1 * (-1) = 0 := by
  norm_num

/-- The determinant of the duplicate two-vector Gram matrix vanishes. -/
theorem duplicate_gram_determinant_zero :
    (1 : ℝ) * 1 - 1 ^ 2 = 0 := by
  norm_num

/-- A positive Schur determinant is exactly the strict scalar inequality used
by the insertion gate. -/
theorem positive_schur_determinant_iff
    (A b eta : ℝ) :
    0 < A * b - eta ^ 2 ↔ eta ^ 2 < A * b := by
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

#print axioms lower_bound_restricts_through_isometric_extension
#print axioms insertion_quadratic_positive
#print axioms inserted_pivot_positive
#print axioms duplicate_zero_mode
#print axioms duplicate_gram_determinant_zero
#print axioms positive_schur_determinant_iff

end RHInsertionSchurFinite
end MillenniumBraid
