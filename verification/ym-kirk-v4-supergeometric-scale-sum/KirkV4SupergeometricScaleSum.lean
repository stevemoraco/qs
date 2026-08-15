import Mathlib

/-!
# Supergeometric dyadic scale-sum bound

Finite/real-analysis bridge for the load-bearing scale sum in Kirk v4 Lemma 8.8.
It proves that, for `x >= 1`, the dyadic family `exp (-2^n x)` has total
mass at most `2 exp (-x)`.  This is the exact mechanism that prevents the
sum over arbitrarily many ultraviolet scales from degrading the physical
exponential rate.

This file does not prove any Yang--Mills polymer estimate, continuum limit,
Osterwalder--Schrader reconstruction, mass gap, or Clay statement.
-/

namespace Millennium.YangMills

open scoped BigOperators

/-- Any nonnegative sequence whose next term is at most half its current term
has every finite partial sum bounded by twice its initial value. -/
theorem half_contracting_sum_range_le_two
    (a : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hhalf : ∀ n, 2 * a (n + 1) ≤ a n)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, a n ≤ 2 * a 0 := by
  have htel : ∀ M : ℕ,
      ∑ n ∈ Finset.range M, a n ≤ 2 * (a 0 - a M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ]
        calc
          (∑ n ∈ Finset.range M, a n) + a M
              ≤ 2 * (a 0 - a M) + a M := by
                linarith
          _ ≤ 2 * (a 0 - a (M + 1)) := by
                nlinarith [hhalf M]
  have hM := htel N
  nlinarith [hnonneg N]

/-- Dyadic exponential term appearing after Kirk's unique-coarsest-scale
allocation. -/
noncomputable def dyadicExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((2 : ℝ) ^ n) * x)

/-- On the physical long-distance region `x >= 1`, the first exponential term
is at most one half. -/
theorem exp_neg_le_half {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-x) ≤ (1 : ℝ) / 2 := by
  have hexp : 2 ≤ Real.exp x := by
    have hbasic := Real.add_one_le_exp x
    nlinarith
  have hmul : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- Every dyadic term is bounded by the first one. -/
theorem dyadicExpTerm_le_first (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    dyadicExpTerm x n ≤ Real.exp (-x) := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  apply Real.exp_monotone
  nlinarith

/-- The dyadic exponential sequence squares at each successive scale. -/
theorem dyadicExpTerm_succ_sq (x : ℝ) (n : ℕ) :
    dyadicExpTerm x (n + 1) = (dyadicExpTerm x n) ^ 2 := by
  simp only [dyadicExpTerm, pow_two]
  rw [← Real.exp_add]
  congr 1
  rw [pow_succ]
  ring

/-- On `x >= 1`, each successive dyadic exponential is at most half the
preceding term. -/
theorem dyadicExpTerm_half_step (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    2 * dyadicExpTerm x (n + 1) ≤ dyadicExpTerm x n := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hfirst : dyadicExpTerm x n ≤ (1 : ℝ) / 2 :=
    (dyadicExpTerm_le_first x hx0 n).trans (exp_neg_le_half hx)
  have hpos : 0 ≤ dyadicExpTerm x n := (Real.exp_pos _).le
  rw [dyadicExpTerm_succ_sq]
  nlinarith

/-- Finite-depth form of the exact supergeometric bound used in Kirk v4
Lemma 8.8. -/
theorem dyadic_exp_sum_range_le_two_exp_neg
    (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range N, dyadicExpTerm x n ≤
      2 * Real.exp (-x) := by
  simpa [dyadicExpTerm] using
    half_contracting_sum_range_le_two
      (dyadicExpTerm x)
      (fun n => (Real.exp_pos _).le)
      (dyadicExpTerm_half_step x hx)
      N

/-- Infinite-depth form: the whole dyadic weak-scale tail is bounded by twice
the coarsest-scale exponential once the dimensionless separation is at least
one. -/
theorem dyadic_exp_tsum_le_two_exp_neg
    (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℕ, dyadicExpTerm x n) ≤ 2 * Real.exp (-x) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact (Real.exp_pos _).le
  · intro N
    exact dyadic_exp_sum_range_le_two_exp_neg x hx N

#print axioms half_contracting_sum_range_le_two
#print axioms exp_neg_le_half
#print axioms dyadicExpTerm_le_first
#print axioms dyadicExpTerm_succ_sq
#print axioms dyadicExpTerm_half_step
#print axioms dyadic_exp_sum_range_le_two_exp_neg
#print axioms dyadic_exp_tsum_le_two_exp_neg

end Millennium.YangMills
