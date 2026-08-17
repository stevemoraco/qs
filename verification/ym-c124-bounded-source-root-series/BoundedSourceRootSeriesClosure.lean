import Mathlib

/-!
# Bounded source-root series closure

Finite real-analysis companion to the typed repair for bounded/normalized
source-buffer roots.  Once an analytic per-placement estimate contributes a
fixed nonnegative root constant `M`, and the underlying placement majorant has
uniformly bounded partial sums, multiplying by `M` preserves summability and
the same branch threshold.

Combined with the separately verified two-root envelope
`sum (n+1)^2 m^n <= (1+m)/(1-m)^3`, this shows that a fixed bounded root
operator changes only the prefactor.  It does not prove the analytic BKAR
per-placement estimate, Kirk's Banach-space theorems, Yang--Mills theory, a
mass gap, or a Clay theorem.
-/

open scoped BigOperators

namespace Millennium.YangMills.BoundedSourceRootSeriesClosure

/-- Multiplying every term of a uniformly bounded nonnegative majorant by one
fixed nonnegative root constant preserves the corresponding finite partial-sum
bound. -/
theorem root_prefactor_preserves_partial_sum_bound
    (base rooted : ℕ → ℝ) (M E : ℝ)
    (hM : 0 ≤ M)
    (hdom : ∀ n, rooted n ≤ M * base n)
    (hbase : ∀ N, (∑ n ∈ Finset.range N, base n) ≤ E) :
    ∀ N, (∑ n ∈ Finset.range N, rooted n) ≤ M * E := by
  intro N
  calc
    (∑ n ∈ Finset.range N, rooted n) ≤
        ∑ n ∈ Finset.range N, M * base n := by
      apply Finset.sum_le_sum
      intro n hn
      exact hdom n
    _ = M * (∑ n ∈ Finset.range N, base n) := by
      rw [Finset.mul_sum]
    _ ≤ M * E := mul_le_mul_of_nonneg_left (hbase N) hM

/-- A nonnegative rooted sequence dominated termwise by one fixed root
constant times a uniformly bounded nonnegative base sequence is summable, and
its total mass is bounded by the same root constant times the base envelope. -/
theorem bounded_root_prefactor_series
    (base rooted : ℕ → ℝ) (M E : ℝ)
    (hM : 0 ≤ M)
    (hroot0 : ∀ n, 0 ≤ rooted n)
    (hdom : ∀ n, rooted n ≤ M * base n)
    (hbase : ∀ N, (∑ n ∈ Finset.range N, base n) ≤ E) :
    Summable rooted ∧ (∑' n : ℕ, rooted n) ≤ M * E := by
  have hpartial :
      ∀ N, (∑ n ∈ Finset.range N, rooted n) ≤ M * E :=
    root_prefactor_preserves_partial_sum_bound
      base rooted M E hM hdom hbase
  constructor
  · apply summable_of_sum_range_le
    · exact hroot0
    · exact hpartial
  · apply Real.tsum_le_of_sum_range_le
    · exact hroot0
    · exact hpartial

/-- Explicit specialization to a two-root placement majorant.  The hypothesis
`hgeom` is exactly the finite envelope proved independently in C122. -/
theorem bounded_source_two_root_series
    (rooted : ℕ → ℝ) (M m : ℝ)
    (hM : 0 ≤ M)
    (hroot0 : ∀ n, 0 ≤ rooted n)
    (hdom : ∀ n,
      rooted n ≤ M * ((((n : ℝ) + 1) ^ 2) * m ^ n))
    (hgeom : ∀ N,
      (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2) * m ^ n) ≤
        (1 + m) / (1 - m) ^ 3) :
    Summable rooted ∧
      (∑' n : ℕ, rooted n) ≤ M * ((1 + m) / (1 - m) ^ 3) := by
  exact bounded_root_prefactor_series
    (fun n : ℕ => (((n : ℝ) + 1) ^ 2) * m ^ n)
    rooted M ((1 + m) / (1 - m) ^ 3)
    hM hroot0 hdom hgeom

#print axioms root_prefactor_preserves_partial_sum_bound
#print axioms bounded_root_prefactor_series
#print axioms bounded_source_two_root_series

end Millennium.YangMills.BoundedSourceRootSeriesClosure
