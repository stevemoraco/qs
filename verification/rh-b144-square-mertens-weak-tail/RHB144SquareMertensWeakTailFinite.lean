import Mathlib

/-!
# RH B144 square-Mertens weak-tail finite core

Finite real/Finset algebra only.

Formalized here:
* one-sided negative depth is the exact [0,1]-selector payoff;
* finite selector sums are dominated by total negative depth and the canonical
  hard selector attains equality;
* a one-sided downward drift of size `s` increases negative depth by at most `s`;
* the ordinary two-column incidence Gram has a cross-term and therefore cannot
  equal the intended diagonal incidence energy.

This file does NOT formalize primes, Mertens' theorem, Mellin transforms,
Landau's theorem, zeta, BGST matrices, or RH.
-/

open Finset
open scoped BigOperators

namespace RHB144SquareMertensWeakTailFinite

/-- Negative depth. -/
def negDepth (x : ℝ) : ℝ := max (-x) 0

@[simp] theorem negDepth_nonneg (x : ℝ) : 0 ≤ negDepth x := by
  simp [negDepth]

/-- Every soft selector in `[0,1]` is bounded by negative depth. -/
theorem selector_payoff_le_negDepth
    (x phi : ℝ) (hphi0 : 0 ≤ phi) (hphi1 : phi ≤ 1) :
    -phi * x ≤ negDepth x := by
  by_cases hx : 0 ≤ x
  · have hpay : -phi * x ≤ 0 := by
      have : 0 ≤ phi * x := mul_nonneg hphi0 hx
      linarith
    exact hpay.trans (negDepth_nonneg x)
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hmul : phi * (-x) ≤ 1 * (-x) := by
      exact mul_le_mul_of_nonneg_right hphi1 (by linarith)
    have hdepth : negDepth x = -x := by
      simp [negDepth, hxneg.le]
    rw [hdepth]
    nlinarith

/-- The hard selector `1_{x<0}` attains the negative depth exactly. -/
theorem selector_attains_negDepth (x : ℝ) :
    ∃ phi : ℝ, 0 ≤ phi ∧ phi ≤ 1 ∧ -phi * x = negDepth x := by
  by_cases hx : x < 0
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    simp [negDepth, hx.le]
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hx0 : 0 ≤ x := le_of_not_gt hx
    simp [negDepth, hx0]

/-- Finite soft-selector domination. -/
theorem finite_selector_sum_le_negative_depth
    {ι : Type*} (s : Finset ι) (x phi : ι → ℝ)
    (hphi0 : ∀ i ∈ s, 0 ≤ phi i)
    (hphi1 : ∀ i ∈ s, phi i ≤ 1) :
    (∑ i ∈ s, -(phi i) * x i) ≤ ∑ i ∈ s, negDepth (x i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact selector_payoff_le_negDepth (x i) (phi i) (hphi0 i hi) (hphi1 i hi)

/-- The canonical hard selector attains total finite negative depth. -/
theorem finite_hard_selector_attains
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    let phi : ι → ℝ := fun i => if x i < 0 then 1 else 0
    (∀ i ∈ s, 0 ≤ phi i) ∧
    (∀ i ∈ s, phi i ≤ 1) ∧
    (∑ i ∈ s, -(phi i) * x i) = ∑ i ∈ s, negDepth (x i) := by
  dsimp
  constructor
  · intro i hi
    split <;> norm_num
  constructor
  · intro i hi
    split <;> norm_num
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x i < 0
    · simp [hx, negDepth, hx.le]
    · have hx0 : 0 ≤ x i := le_of_not_gt hx
      simp [hx, negDepth, hx0]

/-- If a state can fall by at most `s`, its negative depth grows by at most `s`. -/
theorem negDepth_one_sided_drift
    (m0 m s : ℝ) (hs : 0 ≤ s) (hmove : m0 - s ≤ m) :
    negDepth m ≤ negDepth m0 + s := by
  unfold negDepth
  apply max_le
  · have h1 : -m ≤ -m0 + s := by linarith
    have h2 : -m0 ≤ max (-m0) 0 := le_max_left _ _
    linarith
  · have h0 : 0 ≤ max (-m0) 0 := le_max_right _ _
    linarith

/-- Hostile two-column witness: an ordinary incidence row creates a cross-term,
so its Gram energy is not the diagonal incidence energy. -/
theorem ordinary_incidence_gram_not_diagonal
    (a : ℝ) (ha : a ≠ 0) :
    (a * 1 + a * (-1)) ^ 2 = 0 ∧
    (a ^ 2 * 1 ^ 2 + a ^ 2 * (-1) ^ 2) = 2 * a ^ 2 ∧
    0 < 2 * a ^ 2 := by
  constructor
  · ring
  constructor
  · ring
  · have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith

#print axioms selector_payoff_le_negDepth
#print axioms selector_attains_negDepth
#print axioms finite_selector_sum_le_negative_depth
#print axioms finite_hard_selector_attains
#print axioms negDepth_one_sided_drift
#print axioms ordinary_incidence_gram_not_diagonal

end RHB144SquareMertensWeakTailFinite
