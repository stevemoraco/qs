import Mathlib

/-!
# RH finite selector and parity-crossing firewalls

This file formalizes the finite algebra behind the positive-excess selector
identity and two exact countermodels. It does not formalize the Weil form,
Suzuki's operator, primes, zeta zeros, integral operators, or RH.
-/

namespace RHOddSectorSelectorFinite

open Finset

variable {ι : Type*} [Fintype ι]

/-- The selector that keeps exactly the positive entries. -/
def positiveSelector (F : ι → ℝ) (i : ι) : ℝ :=
  if 0 < F i then 1 else 0

/-- Every selector in `[0,1]` is bounded termwise by positive excess. -/
theorem selector_term_le_positivePart
    (F θ : ι → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ1 : ∀ i, θ i ≤ 1)
    (i : ι) :
    θ i * F i ≤ max (F i) 0 := by
  by_cases hF : 0 ≤ F i
  · rw [max_eq_left hF]
    exact mul_le_of_le_one_left hF (hθ1 i)
  · have hF' : F i ≤ 0 := le_of_not_ge hF
    rw [max_eq_right hF']
    exact mul_nonpos_of_nonneg_of_nonpos (hθ0 i) hF'

/-- Finite positive-excess upper bound for every `[0,1]` selector. -/
theorem selector_sum_le_positiveExcess
    (F θ : ι → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ1 : ∀ i, θ i ≤ 1) :
    (∑ i, θ i * F i) ≤ ∑ i, max (F i) 0 := by
  exact sum_le_sum fun i _ =>
    selector_term_le_positivePart F θ hθ0 hθ1 i

/-- The positive selector attains the positive-excess upper bound. -/
theorem positiveSelector_term
    (F : ι → ℝ) (i : ι) :
    positiveSelector F i * F i = max (F i) 0 := by
  by_cases hF : 0 < F i
  · simp [positiveSelector, hF, le_of_lt hF]
  · have hF' : F i ≤ 0 := le_of_not_gt hF
    simp [positiveSelector, hF, max_eq_right hF']

/-- Exact finite selector duality. -/
theorem positiveSelector_attains
    (F : ι → ℝ) :
    (∑ i, positiveSelector F i * F i) =
      ∑ i, max (F i) 0 := by
  apply sum_congr rfl
  intro i hi
  exact positiveSelector_term F i

/-- A two-cell zero-total-mass row with nonzero positive excess. -/
def balancedSpike : Bool → ℝ
  | false => 1
  | true => -1

/-- The spike has exactly zero total mass. -/
theorem balancedSpike_total_zero :
    (∑ i : Bool, balancedSpike i) = 0 := by
  norm_num [Fintype.sum_bool, balancedSpike]

/-- Nevertheless its positive excess is one. -/
theorem balancedSpike_positiveExcess :
    (∑ i : Bool, max (balancedSpike i) 0) = 1 := by
  norm_num [Fintype.sum_bool, balancedSpike]

/-- Therefore a correct total-mass identity does not control selector excess. -/
theorem total_mass_does_not_control_positive_excess :
    ∃ F : Bool → ℝ,
      (∑ i, F i) = 0 ∧
      0 < ∑ i, max (F i) 0 := by
  refine ⟨balancedSpike, balancedSpike_total_zero, ?_⟩
  rw [balancedSpike_positiveExcess]
  norm_num

/-- Abstract intermediate-value consumer: once a continuous parity floor is
known to have the intermediate-value property, opposite signs force a zero.
The analytic proof of that property is external to this finite file. -/
theorem zero_crossing_of_interval_property
    (λ : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < λ a)
    (hb : λ b < 0)
    (hiv : ∀ y, y ∈ Set.Icc (λ b) (λ a) →
      ∃ c ∈ Set.uIcc a b, λ c = y) :
    ∃ c ∈ Set.uIcc a b, λ c = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (λ b) (λ a) := by
    constructor <;> linarith
  exact hiv 0 hzero

#print axioms selector_term_le_positivePart
#print axioms selector_sum_le_positiveExcess
#print axioms positiveSelector_term
#print axioms positiveSelector_attains
#print axioms balancedSpike_total_zero
#print axioms balancedSpike_positiveExcess
#print axioms total_mass_does_not_control_positive_excess
#print axioms zero_crossing_of_interval_property

end RHOddSectorSelectorFinite
