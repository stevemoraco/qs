import Mathlib

/-!
# Entropy-stable supergeometric dyadic scale sum

Finite real-analysis bridge for the multiscale source-tree step in Kirk v4
Lemmas 8.6--8.8.

If the absolute combinatorial weight at relative ultraviolet depth `n` grows
at most like `A^n`, while each contribution carries the dyadic physical decay
`exp (-2^n x)`, then after enlarging the long-distance threshold so that
`2 * A * exp (-x) <= 1`, the full infinite weighted tail is still bounded by
`2 * exp (-x)`.  Thus any fixed exponential entropy per relative scale changes
only the distance threshold/prefactor, not the physical exponential rate.

This file does not prove Kirk's source-tree allocation, polymer/root norms,
Yang--Mills continuum construction, Osterwalder--Schrader reconstruction,
mass gap, or any Clay statement.
-/

namespace Millennium.YangMills

open scoped BigOperators

/-- Generic finite geometric-envelope lemma used by the weighted dyadic tail. -/
theorem entropy_half_contracting_sum_range_le_two
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

/-- Unweighted dyadic decay factor. -/
noncomputable def entropyDyadicBaseTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((2 : ℝ) ^ n) * x)

/-- The dyadic base term is nonnegative. -/
theorem entropyDyadicBaseTerm_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ entropyDyadicBaseTerm x n :=
  (Real.exp_pos _).le

/-- On `x >= 0`, every dyadic base term is no larger than the first one. -/
theorem entropyDyadicBaseTerm_le_first
    (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    entropyDyadicBaseTerm x n ≤ Real.exp (-x) := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  apply Real.exp_monotone
  nlinarith

/-- The dyadic base term squares at every successor scale. -/
theorem entropyDyadicBaseTerm_succ_sq (x : ℝ) (n : ℕ) :
    entropyDyadicBaseTerm x (n + 1) = (entropyDyadicBaseTerm x n) ^ 2 := by
  simp only [entropyDyadicBaseTerm, pow_two]
  rw [← Real.exp_add]
  congr 1
  rw [pow_succ]
  ring

/-- Dyadic decay with a fixed exponential multiplicity `A^n`. -/
noncomputable def entropyWeightedDyadicTerm
    (A x : ℝ) (n : ℕ) : ℝ :=
  A ^ n * entropyDyadicBaseTerm x n

/-- Nonnegativity of the entropy-weighted dyadic term. -/
theorem entropyWeightedDyadicTerm_nonneg
    (A x : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    0 ≤ entropyWeightedDyadicTerm A x n := by
  exact mul_nonneg (pow_nonneg hA n) (entropyDyadicBaseTerm_nonneg x n)

/-- Exact successor factorization of the entropy-weighted term. -/
theorem entropyWeightedDyadicTerm_succ
    (A x : ℝ) (n : ℕ) :
    entropyWeightedDyadicTerm A x (n + 1) =
      entropyWeightedDyadicTerm A x n *
        (A * entropyDyadicBaseTerm x n) := by
  simp only [entropyWeightedDyadicTerm]
  rw [entropyDyadicBaseTerm_succ_sq, pow_succ]
  ring

/-- A source-friendly sufficient condition for the weighted contraction:
`2*A <= exp x` implies `2*A*exp(-x) <= 1`. -/
theorem two_mul_exp_neg_le_one_of_two_mul_le_exp
    (A x : ℝ)
    (hbound : 2 * A ≤ Real.exp x) :
    2 * A * Real.exp (-x) ≤ 1 := by
  have hpos : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  calc
    2 * A * Real.exp (-x)
        ≤ Real.exp x * Real.exp (-x) := by
          exact mul_le_mul_of_nonneg_right hbound hpos
    _ = 1 := by
      rw [← Real.exp_add]
      simp

/-- Once `2*A*exp(-x) <= 1`, every weighted successor is at most half
its predecessor. -/
theorem entropyWeightedDyadicTerm_half_step
    (A x : ℝ)
    (hA : 0 ≤ A)
    (hx : 0 ≤ x)
    (hcontract : 2 * A * Real.exp (-x) ≤ 1)
    (n : ℕ) :
    2 * entropyWeightedDyadicTerm A x (n + 1) ≤
      entropyWeightedDyadicTerm A x n := by
  have hbase := entropyDyadicBaseTerm_le_first x hx n
  have h2A : 0 ≤ 2 * A := by nlinarith
  have hratio : 2 * A * entropyDyadicBaseTerm x n ≤ 1 := by
    calc
      2 * A * entropyDyadicBaseTerm x n
          ≤ 2 * A * Real.exp (-x) := by
            exact mul_le_mul_of_nonneg_left hbase h2A
      _ ≤ 1 := hcontract
  have hterm : 0 ≤ entropyWeightedDyadicTerm A x n :=
    entropyWeightedDyadicTerm_nonneg A x hA n
  rw [entropyWeightedDyadicTerm_succ]
  calc
    2 *
          (entropyWeightedDyadicTerm A x n *
            (A * entropyDyadicBaseTerm x n))
        = entropyWeightedDyadicTerm A x n *
            (2 * A * entropyDyadicBaseTerm x n) := by ring
    _ ≤ entropyWeightedDyadicTerm A x n * 1 := by
      exact mul_le_mul_of_nonneg_left hratio hterm
    _ = entropyWeightedDyadicTerm A x n := by ring

/-- Finite-depth entropy-stable scale sum. -/
theorem entropy_weighted_dyadic_sum_range_le_two_exp_neg
    (A x : ℝ)
    (hA : 0 ≤ A)
    (hx : 0 ≤ x)
    (hcontract : 2 * A * Real.exp (-x) ≤ 1)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, entropyWeightedDyadicTerm A x n ≤
      2 * Real.exp (-x) := by
  simpa [entropyWeightedDyadicTerm, entropyDyadicBaseTerm] using
    entropy_half_contracting_sum_range_le_two
      (entropyWeightedDyadicTerm A x)
      (entropyWeightedDyadicTerm_nonneg A x hA)
      (entropyWeightedDyadicTerm_half_step A x hA hx hcontract)
      N

/-- Infinite-depth entropy-stable scale sum.  Any fixed exponential
multiplicity `A^n` is harmless after the physical separation is large enough
that `2*A*exp(-x) <= 1`. -/
theorem entropy_weighted_dyadic_tsum_le_two_exp_neg
    (A x : ℝ)
    (hA : 0 ≤ A)
    (hx : 0 ≤ x)
    (hcontract : 2 * A * Real.exp (-x) ≤ 1) :
    (∑' n : ℕ, entropyWeightedDyadicTerm A x n) ≤
      2 * Real.exp (-x) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact entropyWeightedDyadicTerm_nonneg A x hA n
  · intro N
    exact entropy_weighted_dyadic_sum_range_le_two_exp_neg
      A x hA hx hcontract N

/-- Convenient threshold form: `2*A <= exp x` is sufficient to retain the
full coarsest-scale exponent in the weighted infinite tail. -/
theorem entropy_weighted_dyadic_tsum_le_two_exp_neg_of_two_mul_le_exp
    (A x : ℝ)
    (hA : 0 ≤ A)
    (hx : 0 ≤ x)
    (hbound : 2 * A ≤ Real.exp x) :
    (∑' n : ℕ, entropyWeightedDyadicTerm A x n) ≤
      2 * Real.exp (-x) := by
  exact entropy_weighted_dyadic_tsum_le_two_exp_neg
    A x hA hx (two_mul_exp_neg_le_one_of_two_mul_le_exp A x hbound)

/-- A fixed nonnegative overall prefactor changes only the prefactor, not the
physical exponential rate. -/
theorem entropy_weighted_dyadic_tsum_with_prefactor
    (M A x : ℝ)
    (hM : 0 ≤ M)
    (hA : 0 ≤ A)
    (hx : 0 ≤ x)
    (hbound : 2 * A ≤ Real.exp x) :
    M * (∑' n : ℕ, entropyWeightedDyadicTerm A x n) ≤
      2 * M * Real.exp (-x) := by
  have hsum := entropy_weighted_dyadic_tsum_le_two_exp_neg_of_two_mul_le_exp
    A x hA hx hbound
  calc
    M * (∑' n : ℕ, entropyWeightedDyadicTerm A x n)
        ≤ M * (2 * Real.exp (-x)) := by
          exact mul_le_mul_of_nonneg_left hsum hM
    _ = 2 * M * Real.exp (-x) := by ring

#print axioms entropy_half_contracting_sum_range_le_two
#print axioms entropyDyadicBaseTerm_nonneg
#print axioms entropyDyadicBaseTerm_le_first
#print axioms entropyDyadicBaseTerm_succ_sq
#print axioms entropyWeightedDyadicTerm_nonneg
#print axioms entropyWeightedDyadicTerm_succ
#print axioms two_mul_exp_neg_le_one_of_two_mul_le_exp
#print axioms entropyWeightedDyadicTerm_half_step
#print axioms entropy_weighted_dyadic_sum_range_le_two_exp_neg
#print axioms entropy_weighted_dyadic_tsum_le_two_exp_neg
#print axioms entropy_weighted_dyadic_tsum_le_two_exp_neg_of_two_mul_le_exp
#print axioms entropy_weighted_dyadic_tsum_with_prefactor

end Millennium.YangMills
