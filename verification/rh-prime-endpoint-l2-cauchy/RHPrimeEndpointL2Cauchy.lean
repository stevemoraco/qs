import Mathlib

/-!
# RH prime-endpoint weighted L2 bridge

This file formalizes the finite weighted Cauchy--Schwarz step in the banked
prime-endpoint `L^2` reformulation of the B54 RH criterion.

It does not formalize primes, the Chebyshev function, the prime number theorem,
the von-Koch estimate, the parent B54 equivalence, or RH.
-/

open scoped BigOperators

namespace RHPrimeEndpointL2Cauchy

/-- The positive part of a real number is bounded by its absolute value. -/
theorem positivePart_le_abs (x : ℝ) : max x 0 ≤ |x| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', abs_of_nonpos hx']
    exact neg_nonneg.mpr hx'

/-- Weighted Cauchy--Schwarz in the exact form needed before replacing the
positive part by an absolute value. -/
theorem weighted_abs_cauchy {ι : Type*}
    (s : Finset ι) (w b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * |b i|) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (b i) ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw ?_ ?_
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    rw [mul_pow, sq_abs]
    ring_nf
    exact le_rfl

/-- Prime-entry positive mass is controlled by total weight times the weighted
block square mass. This is the finite implication

`(sum w_i [b_i]_+)^2 ≤ (sum w_i)(sum w_i b_i^2)`.
-/
theorem weighted_positivePart_cauchy {ι : Type*}
    (s : Finset ι) (w b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * max (b i) 0) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (b i) ^ 2) := by
  have hpoint : ∀ i ∈ s,
      w i * max (b i) 0 ≤ w i * |b i| := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (positivePart_le_abs (b i)) (hw i hi)
  have hsum :
      (∑ i ∈ s, w i * max (b i) 0) ≤
        ∑ i ∈ s, w i * |b i| :=
    Finset.sum_le_sum hpoint
  have hleft_nonneg :
      0 ≤ ∑ i ∈ s, w i * max (b i) 0 := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (le_max_right _ _)
  have hright_nonneg :
      0 ≤ ∑ i ∈ s, w i * |b i| := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (abs_nonneg _)
  have hsquares :
      (∑ i ∈ s, w i * max (b i) 0) ^ 2 ≤
        (∑ i ∈ s, w i * |b i|) ^ 2 := by
    nlinarith
  exact hsquares.trans (weighted_abs_cauchy s w b hw)

/-- Scalar endgame: if total weight is at most `W`, the weighted square mass
is at most `T`, and the positive mass has nonnegative square, then the latter
is bounded by `W*T`. -/
theorem positive_mass_sq_le_of_budgets
    {S weight square W T : ℝ}
    (hS : S ^ 2 ≤ weight * square)
    (hweight_nonneg : 0 ≤ weight)
    (hsquare_nonneg : 0 ≤ square)
    (hweight : weight ≤ W)
    (hsquare : square ≤ T) :
    S ^ 2 ≤ W * T := by
  calc
    S ^ 2 ≤ weight * square := hS
    _ ≤ W * square := mul_le_mul_of_nonneg_right hweight hsquare_nonneg
    _ ≤ W * T := by
      have hW : 0 ≤ W := hweight_nonneg.trans hweight
      exact mul_le_mul_of_nonneg_left hsquare hW

#print axioms positivePart_le_abs
#print axioms weighted_abs_cauchy
#print axioms weighted_positivePart_cauchy
#print axioms positive_mass_sq_le_of_budgets

end RHPrimeEndpointL2Cauchy
