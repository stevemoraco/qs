import Mathlib

/-!
# RH B109 weight-free ordinary-prime increment finite core

Finite real algebra only.

This file formalizes the load-bearing finite inequalities used by B109:

* positive-part stability under an additive perturbation;
* cumulative positive-variation stability under a finite error debt;
* finite selector domination and exact binary-selector attainment;
* the scalar negative-depth identity used by the rank-one matrix landing.

It deliberately does not formalize primes, Chebyshev bounds, proper-power shell
estimates, B98 interpolation, B46A/Landau, zeta zeros, or RH.
-/

open Finset
open scoped BigOperators

namespace RHB109WeightFreePrimeIncrementFinite

/-- Positive part of a real scalar. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Negative spectral depth of a scalar. -/
def negDepth (x : ℝ) : ℝ := posPart (-x)

@[simp] theorem posPart_nonneg (x : ℝ) : 0 ≤ posPart x := by
  exact le_max_right x 0

/-- Adding an error can increase the positive part by at most the error magnitude. -/
theorem posPart_add_le (x r : ℝ) :
    posPart (x + r) ≤ posPart x + |r| := by
  have hx : x ≤ posPart x := le_max_left x 0
  have hr : r ≤ |r| := le_abs_self r
  have hsum : x + r ≤ posPart x + |r| := add_le_add hx hr
  have hzero : 0 ≤ posPart x + |r| :=
    add_nonneg (posPart_nonneg x) (abs_nonneg r)
  exact max_le hsum hzero

/-- Removing an error changes the positive part by at most the same magnitude. -/
theorem posPart_le_add (x r : ℝ) :
    posPart x ≤ posPart (x + r) + |r| := by
  have hx : x + r ≤ posPart (x + r) := le_max_left (x + r) 0
  have hr : -r ≤ |r| := neg_le_abs r
  have hsum : x ≤ posPart (x + r) + |r| := by
    linarith
  exact hsum

/-- Exact Lipschitz firewall for the positive part. -/
theorem abs_posPart_add_sub_le (x r : ℝ) :
    |posPart (x + r) - posPart x| ≤ |r| := by
  rw [abs_le]
  constructor
  · have h := posPart_le_add x r
    linarith
  · have h := posPart_add_le x r
    linarith

/-- Finite cumulative positive variation survives an additive perturbation with
only the sum of absolute perturbations as debt. -/
theorem sum_posPart_add_le
    {ι : Type*} (s : Finset ι) (x r : ι → ℝ) :
    (∑ i ∈ s, posPart (x i + r i)) ≤
      (∑ i ∈ s, posPart (x i)) + (∑ i ∈ s, |r i|) := by
  calc
    (∑ i ∈ s, posPart (x i + r i))
        ≤ ∑ i ∈ s, (posPart (x i) + |r i|) := by
          apply Finset.sum_le_sum
          intro i hi
          exact posPart_add_le (x i) (r i)
    _ = (∑ i ∈ s, posPart (x i)) + (∑ i ∈ s, |r i|) := by
      rw [Finset.sum_add_distrib]

/-- Reverse finite cumulative perturbation bound. -/
theorem sum_posPart_le_add
    {ι : Type*} (s : Finset ι) (x r : ι → ℝ) :
    (∑ i ∈ s, posPart (x i)) ≤
      (∑ i ∈ s, posPart (x i + r i)) + (∑ i ∈ s, |r i|) := by
  calc
    (∑ i ∈ s, posPart (x i))
        ≤ ∑ i ∈ s, (posPart (x i + r i) + |r i|) := by
          apply Finset.sum_le_sum
          intro i hi
          exact posPart_le_add (x i) (r i)
    _ = (∑ i ∈ s, posPart (x i + r i)) + (∑ i ∈ s, |r i|) := by
      rw [Finset.sum_add_distrib]

/-- A selector with coefficients in `[0,1]` never exceeds positive variation. -/
theorem selector_le_posPart
    {ι : Type*} (s : Finset ι) (x phi : ι → ℝ)
    (hphi0 : ∀ i ∈ s, 0 ≤ phi i)
    (hphi1 : ∀ i ∈ s, phi i ≤ 1) :
    (∑ i ∈ s, phi i * x i) ≤ ∑ i ∈ s, posPart (x i) := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : 0 ≤ x i
  · have hmul : phi i * x i ≤ 1 * x i :=
      mul_le_mul_of_nonneg_right (hphi1 i hi) hx
    simpa [posPart, max_eq_left hx] using hmul
  · have hx' : x i ≤ 0 := le_of_not_ge hx
    have hmul : phi i * x i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hphi0 i hi) hx'
    simpa [posPart, max_eq_right hx'] using hmul

/-- The binary sign selector attains the positive variation exactly. -/
theorem binary_selector_attains_posPart
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, (if 0 < x i then (1 : ℝ) else 0) * x i) =
      ∑ i ∈ s, posPart (x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : 0 < x i
  · have hx0 : 0 ≤ x i := le_of_lt hx
    simp [hx, posPart, max_eq_left hx0]
  · have hx0 : x i ≤ 0 := le_of_not_gt hx
    simp [hx, posPart, max_eq_right hx0]

/-- Finite perturbation terminal: a prime-only variation budget plus an absolute
proper-power/error budget controls the full variation. -/
theorem variation_budget_transfer
    (primeVar errorDebt fullVar primeBudget errorBudget : ℝ)
    (hfull : fullVar ≤ primeVar + errorDebt)
    (hprime : primeVar ≤ primeBudget)
    (herror : errorDebt ≤ errorBudget) :
    fullVar ≤ primeBudget + errorBudget := by
  linarith

/-- Rank-one scalar landing: negative depth of `-x` is exactly the positive part
of `x`. -/
@[simp] theorem negDepth_neg_eq_posPart (x : ℝ) :
    negDepth (-x) = posPart x := by
  simp [negDepth, posPart]

/-- A finite scalar Loewner threshold is just an upper bound. -/
theorem scalar_shift_nonnegative_iff (C x : ℝ) :
    0 ≤ C - x ↔ x ≤ C := by
  linarith

#print axioms posPart_nonneg
#print axioms posPart_add_le
#print axioms posPart_le_add
#print axioms abs_posPart_add_sub_le
#print axioms sum_posPart_add_le
#print axioms sum_posPart_le_add
#print axioms selector_le_posPart
#print axioms binary_selector_attains_posPart
#print axioms variation_budget_transfer
#print axioms negDepth_neg_eq_posPart
#print axioms scalar_shift_nonnegative_iff

end RHB109WeightFreePrimeIncrementFinite
