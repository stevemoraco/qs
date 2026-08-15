import Mathlib

/-!
# B105 prime-gap weighted finite core

Finite real algebra only.  This file formalizes the load-bearing selector,
weight-change, and scalar negative-depth identities used by the human B105
prime-gap sparsification theorem in `stevemoraco/RH`.

It deliberately does NOT formalize prime numbers, Stadlmann's mean-square gap
theorem, Chebyshev estimates, the B46 explicit formula, Landau's theorem, zeta,
or the Riemann hypothesis.
-/

open Finset
open scoped BigOperators

namespace RHB105PrimeGapWeightedFinite

/-- Scalar positive part. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- The endogenous binary selector which realizes the positive part. -/
def positiveSelector (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

@[simp] theorem posPart_nonneg (x : ℝ) : 0 ≤ posPart x := by
  simp [posPart]

/-- Every box selector `0 <= phi <= 1` lies below the scalar positive part. -/
theorem selector_term_le_posPart
    {x phi : ℝ} (hphi0 : 0 ≤ phi) (hphi1 : phi ≤ 1) :
    phi * x ≤ posPart x := by
  by_cases hx : 0 ≤ x
  · rw [posPart, max_eq_left hx]
    have hprod : 0 ≤ (1 - phi) * x :=
      mul_nonneg (sub_nonneg.mpr hphi1) hx
    nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [posPart, max_eq_right hx']
    exact mul_nonpos_of_nonneg_of_nonpos hphi0 hx'

/-- The endogenous binary selector attains the positive part exactly. -/
theorem positiveSelector_mul (x : ℝ) :
    positiveSelector x * x = posPart x := by
  by_cases hx : 0 ≤ x
  · simp [positiveSelector, posPart, hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [positiveSelector, posPart, hx, max_eq_right hx']

/-- Weighted finite selector domination.  This is the finite support-function
half of the B105 signed-dispersion duality. -/
theorem weighted_selector_sum_le
    {ι : Type*} (s : Finset ι)
    (w phi x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hphi0 : ∀ i ∈ s, 0 ≤ phi i)
    (hphi1 : ∀ i ∈ s, phi i ≤ 1) :
    (∑ i ∈ s, w i * (phi i * x i)) ≤
      ∑ i ∈ s, w i * posPart (x i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (selector_term_le_posPart (hphi0 i hi) (hphi1 i hi))
    (hw i hi)

/-- The endogenous selector attains the weighted positive-part sum exactly. -/
theorem weighted_positiveSelector_attains
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ) :
    (∑ i ∈ s, w i * (positiveSelector (x i) * x i)) =
      ∑ i ∈ s, w i * posPart (x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [positiveSelector_mul]

/-- Hence the finite positive-part functional is exactly the maximum over its
explicit endogenous box selector; no arbitrary unsigned majorant is needed. -/
theorem weighted_selector_exact_certificate
    {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∀ phi : ι → ℝ,
      (∀ i ∈ s, 0 ≤ phi i) →
      (∀ i ∈ s, phi i ≤ 1) →
      (∑ i ∈ s, w i * (phi i * x i)) ≤
        ∑ i ∈ s, w i * posPart (x i)) ∧
    (∑ i ∈ s, w i * (positiveSelector (x i) * x i)) =
      ∑ i ∈ s, w i * posPart (x i) := by
  constructor
  · intro phi h0 h1
    exact weighted_selector_sum_le s w phi x hw h0 h1
  · exact weighted_positiveSelector_attains s w x

/-- Finite weight replacement budget.  If `delta <= w`, the excess paid by
replacing `delta` by `w` is controlled by `(w-delta) E`. -/
theorem weight_change_term_budget
    {delta w E r M : ℝ}
    (hdelta : delta ≤ w)
    (hr : w - delta ≤ r)
    (hr0 : 0 ≤ r)
    (hE0 : 0 ≤ E)
    (hEM : E ≤ M) :
    0 ≤ w * E - delta * E ∧
      w * E - delta * E ≤ r * M := by
  have hdiff0 : 0 ≤ w - delta := sub_nonneg.mpr hdelta
  have hfirst : 0 ≤ (w - delta) * E := mul_nonneg hdiff0 hE0
  have hsecond : (w - delta) * E ≤ r * M :=
    mul_le_mul hr hEM hE0 hr0
  constructor
  · nlinarith
  · nlinarith

/-- Finite summed version of the weight-replacement budget. -/
theorem weighted_sum_change_budget
    {ι : Type*} (s : Finset ι)
    (delta w E r M : ι → ℝ)
    (hdelta : ∀ i ∈ s, delta i ≤ w i)
    (hr : ∀ i ∈ s, w i - delta i ≤ r i)
    (hr0 : ∀ i ∈ s, 0 ≤ r i)
    (hE0 : ∀ i ∈ s, 0 ≤ E i)
    (hEM : ∀ i ∈ s, E i ≤ M i) :
    (∑ i ∈ s, (w i * E i - delta i * E i)) ≤
      ∑ i ∈ s, r i * M i := by
  apply Finset.sum_le_sum
  intro i hi
  exact (weight_change_term_budget
    (hdelta i hi) (hr i hi) (hr0 i hi) (hE0 i hi) (hEM i hi)).2

/-- Scalar negative spectral depth. -/
def negDepth (x : ℝ) : ℝ := max (-x) 0

/-- The B105 marked matrix scalar has negative depth equal to the shell excess. -/
theorem barrier_shell_negative_depth (B U : ℝ) :
    negDepth (B - U) = posPart (U - B) := by
  simp [negDepth, posPart]

/-- A shifted rank-one negative-index event is exactly a scalar depth threshold. -/
theorem shifted_negative_event_iff
    (B U y : ℝ) :
    B + y - U < 0 ↔ y < U - B := by
  linarith

/-- The threshold interval has no negative depth once the shift reaches the
full scalar excursion. -/
theorem shift_past_excursion_nonnegative
    {B U y : ℝ} (hy : U - B ≤ y) :
    0 ≤ B + y - U := by
  linarith

/-- Abstract firewall: a zero-threshold sign bit cannot determine excursion
magnitude.  Both numbers are negative but their depths are different. -/
theorem same_negative_index_different_depth
    {a b : ℝ} (ha : 0 < a) (hb : a < b) :
    (-a < 0) ∧ (-b < 0) ∧ negDepth (-a) < negDepth (-b) := by
  have hb0 : 0 < b := lt_trans ha hb
  constructor
  · linarith
  constructor
  · linarith
  · simp [negDepth, ha.le, hb0.le]
    exact hb

#print axioms posPart_nonneg
#print axioms selector_term_le_posPart
#print axioms positiveSelector_mul
#print axioms weighted_selector_sum_le
#print axioms weighted_positiveSelector_attains
#print axioms weighted_selector_exact_certificate
#print axioms weight_change_term_budget
#print axioms weighted_sum_change_budget
#print axioms barrier_shell_negative_depth
#print axioms shifted_negative_event_iff
#print axioms shift_past_excursion_nonnegative
#print axioms same_negative_index_different_depth

end RHB105PrimeGapWeightedFinite
