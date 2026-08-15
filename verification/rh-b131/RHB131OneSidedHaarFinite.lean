import Mathlib

open Finset
open scoped BigOperators

/-!
# RH B131 one-sided Haar finite core

Finite real/Finset algebra only.

This file records load-bearing finite identities behind the B131 reduction:

* a nonnegative selector bounded by one is dominated by the positive part;
* the sign selector attains the positive-part sum exactly;
* bounded additive perturbations move positive parts by at most their absolute error;
* nonnegative cell lengths commute with positive-part scaling;
* a diagonal negative-depth sum is exactly the weighted positive cell mass.

It does **not** formalize prime sums, the Haar channel, Mellin transforms,
Landau's theorem, zeta, the B46 explicit formula, or RH.
-/

namespace RHB131OneSidedHaarFinite

/-- Positive part. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Scalar negative depth, matching the negative eigenvalue mass of a 1x1 form. -/
def negDepth (x : ℝ) : ℝ := max (-x) 0

/-- The hard selector attaining the positive part. -/
def signSelector (x : ℝ) : ℝ := if 0 < x then 1 else 0

@[simp] theorem signSelector_nonneg (x : ℝ) :
    0 ≤ signSelector x := by
  by_cases h : 0 < x <;> simp [signSelector, h]

@[simp] theorem signSelector_le_one (x : ℝ) :
    signSelector x ≤ 1 := by
  by_cases h : 0 < x <;> simp [signSelector, h]

/-- The hard selector recovers the positive part pointwise. -/
theorem signSelector_mul (x : ℝ) :
    signSelector x * x = posPart x := by
  by_cases h : 0 < x
  · simp [signSelector, h, posPart, max_eq_left h.le]
  · have hx : x ≤ 0 := le_of_not_gt h
    simp [signSelector, h, posPart, max_eq_right hx]

/-- Every selector in `[0,1]` is pointwise dominated by the positive part. -/
theorem selector_mul_le_posPart
    {x φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    φ * x ≤ posPart x := by
  by_cases hx : 0 ≤ x
  · rw [posPart, max_eq_left hx]
    simpa using (mul_le_mul_of_nonneg_right hφ1 hx)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [posPart, max_eq_right hx']
    exact mul_nonpos_of_nonneg_of_nonpos hφ0 hx'

/-- Weighted finite selector domination. -/
theorem weighted_selector_le_positive_part
    {ι : Type*} (s : Finset ι) (w x φ : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hφ0 : ∀ i ∈ s, 0 ≤ φ i)
    (hφ1 : ∀ i ∈ s, φ i ≤ 1) :
    ∑ i ∈ s, w i * (φ i * x i) ≤
      ∑ i ∈ s, w i * posPart (x i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (selector_mul_le_posPart (hφ0 i hi) (hφ1 i hi)) (hw i hi)

/-- The sign selector attains the weighted positive-part sum exactly. -/
theorem weighted_selector_attains_positive_part
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ) :
    ∑ i ∈ s, w i * (signSelector (x i) * x i) =
      ∑ i ∈ s, w i * posPart (x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [signSelector_mul]

/-- Positive parts are 1-Lipschitz under additive perturbation. -/
theorem posPart_le_posPart_add_abs (x y : ℝ) :
    posPart x ≤ posPart y + |x - y| := by
  have hxy : x ≤ y + |x - y| := by
    have h := le_abs_self (x - y)
    linarith
  have hy : y ≤ posPart y := by
    exact le_max_left y 0
  have h0 : 0 ≤ posPart y + |x - y| := by
    have hp : 0 ≤ posPart y := le_max_right y 0
    positivity
  apply max_le
  · linarith
  · exact h0

/-- Nonnegative scaling commutes with the positive part. -/
theorem posPart_scaled
    {ell x : ℝ} (hell : 0 ≤ ell) :
    posPart (ell * x) = ell * posPart x := by
  by_cases hx : 0 ≤ x
  · have hprod : 0 ≤ ell * x := mul_nonneg hell hx
    rw [posPart, max_eq_left hprod, posPart, max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hprod : ell * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hell hx'
    rw [posPart, max_eq_right hprod, posPart, max_eq_right hx']
    ring

/-- A scalar diagonal entry `-ell*x` has negative depth `ell * x_+`. -/
theorem cell_negative_depth_identity
    {ell x : ℝ} (hell : 0 ≤ ell) :
    negDepth (-ell * x) = ell * posPart x := by
  rw [negDepth]
  have hneg : -(-ell * x) = ell * x := by ring
  rw [hneg, posPart_scaled hell]

/-- Finite diagonal negative mass equals weighted positive cell mass. -/
theorem finite_cell_negative_depth_sum
    {ι : Type*} (s : Finset ι) (ell x : ι → ℝ)
    (hell : ∀ i ∈ s, 0 ≤ ell i) :
    ∑ i ∈ s, negDepth (-ell i * x i) =
      ∑ i ∈ s, ell i * posPart (x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact cell_negative_depth_identity (hell i hi)

#print axioms signSelector_mul
#print axioms selector_mul_le_posPart
#print axioms weighted_selector_le_positive_part
#print axioms weighted_selector_attains_positive_part
#print axioms posPart_le_posPart_add_abs
#print axioms posPart_scaled
#print axioms finite_cell_negative_depth_sum

end RHB131OneSidedHaarFinite
