import Mathlib

namespace YMDet2SpectralProductFinite

/-!
# Finite product core for the repaired self-adjoint `det₂` lower bound

The accompanying human theorem proves the scalar analytic inequality

`exp (-(a^2)/(2*δ)) ≤ |(1-a) exp a|`

for real eigenvalues satisfying a quantitative distance condition from `1`.
This file formalizes only the exact finite aggregation of those per-eigenvalue
bounds and the exponential sum/product identity.

It does **not** formalize the scalar logarithmic inequality, compact
self-adjoint spectral theory, Hilbert--Schmidt operators, convergence of the
modified Fredholm determinant, Yang--Mills theory, or a mass gap.
-/

/-- One real-eigenvalue factor in the modified Fredholm determinant. -/
noncomputable def det2Factor (a : ℝ) : ℝ :=
  |(1 - a) * Real.exp a|

/-- The per-eigenvalue lower factor supplied by the external scalar theorem. -/
noncomputable def spectralLowerFactor (δ a : ℝ) : ℝ :=
  Real.exp (-(a ^ 2) / (2 * δ))

/-- Every spectral lower factor is strictly positive. -/
theorem spectralLowerFactor_pos (δ a : ℝ) :
    0 < spectralLowerFactor δ a := by
  exact Real.exp_pos _

/-- Every scalar determinant factor is nonnegative. -/
theorem det2Factor_nonneg (a : ℝ) :
    0 ≤ det2Factor a := by
  exact abs_nonneg _

/-- A finite product of spectral lower factors is nonnegative. -/
theorem spectralLowerProduct_nonneg (δ : ℝ) (xs : List ℝ) :
    0 ≤ (xs.map (spectralLowerFactor δ)).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (le_of_lt (spectralLowerFactor_pos δ a)) ih

/-- Pointwise scalar determinant lower bounds multiply over every finite
real-eigenvalue list. -/
theorem finite_det2_product_lower_bound
    (δ : ℝ) (xs : List ℝ)
    (hfactor : ∀ a ∈ xs,
      spectralLowerFactor δ a ≤ det2Factor a) :
    (xs.map (spectralLowerFactor δ)).prod ≤
      (xs.map det2Factor).prod := by
  revert hfactor
  induction xs with
  | nil => simp
  | cons a xs ih =>
      intro hfactor
      simp only [List.map_cons, List.prod_cons]
      apply mul_le_mul
      · exact hfactor a (by simp)
      · exact ih (fun b hb => hfactor b (by simp [hb]))
      · exact spectralLowerProduct_nonneg δ xs
      · exact det2Factor_nonneg a

/-- The product of the lower factors is exactly the exponential of the
negative finite square budget. -/
theorem spectralLowerProduct_eq_exp_squareSum
    (δ : ℝ) (xs : List ℝ) :
    (xs.map (spectralLowerFactor δ)).prod =
      Real.exp (-((xs.map (fun a : ℝ => a ^ 2)).sum) / (2 * δ)) := by
  induction xs with
  | nil => simp [spectralLowerFactor]
  | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih]
      simp only [spectralLowerFactor]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Finite determinant aggregation in the exact form used by the repaired
self-adjoint spectral-distance theorem. -/
theorem finite_det2_lower_bound_from_scalar
    (δ : ℝ) (xs : List ℝ)
    (hfactor : ∀ a ∈ xs,
      spectralLowerFactor δ a ≤ det2Factor a) :
    Real.exp (-((xs.map (fun a : ℝ => a ^ 2)).sum) / (2 * δ)) ≤
      (xs.map det2Factor).prod := by
  rw [← spectralLowerProduct_eq_exp_squareSum δ xs]
  exact finite_det2_product_lower_bound δ xs hfactor

#print axioms spectralLowerFactor_pos
#print axioms det2Factor_nonneg
#print axioms spectralLowerProduct_nonneg
#print axioms finite_det2_product_lower_bound
#print axioms spectralLowerProduct_eq_exp_squareSum
#print axioms finite_det2_lower_bound_from_scalar

end YMDet2SpectralProductFinite
