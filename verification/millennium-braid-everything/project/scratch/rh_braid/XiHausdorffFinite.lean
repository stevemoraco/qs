import Mathlib

open scoped BigOperators

namespace Millennium
namespace XiHausdorff

/-- The finite moment sequence associated to nonnegative weights and nodes. -/
def moment {ι : Type*} [Fintype ι]
    (w y : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, w i * (y i) ^ n

/-- `hausdorffDiff k a n` is the k-fold operator `a n - a (n+1)`, i.e.
`(-1)^k Δ^k a_n` in the usual forward-difference convention. -/
def hausdorffDiff : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, a, n => a n
  | k + 1, a, n => hausdorffDiff k a n - hausdorffDiff k a (n + 1)

/-- Exact finite Hausdorff identity:

`(-1)^k Δ^k a_n = Σ_i w_i y_i^n (1-y_i)^k`

for a finite moment sequence `a_n = Σ_i w_i y_i^n`. -/
theorem hausdorffDiff_moment {ι : Type*} [Fintype ι]
    (w y : ι → ℝ) (n k : ℕ) :
    hausdorffDiff k (moment w y) n =
      ∑ i, w i * (y i) ^ n * (1 - y i) ^ k := by
  induction k generalizing n with
  | zero =>
      simp [hausdorffDiff, moment]
  | succ k ih =>
      change
        hausdorffDiff k (moment w y) n -
            hausdorffDiff k (moment w y) (n + 1) =
          ∑ i, w i * (y i) ^ n * (1 - y i) ^ (k + 1)
      rw [ih, ih]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ (y i) n, pow_succ (1 - y i) k]
      ring

/-- Finite Hausdorff positivity. This is the Lean-verifiable core used by the
xi-log-derivative moment criterion; it does not encode the analytic converse or
prove RH. -/
theorem hausdorffDiff_moment_nonneg {ι : Type*} [Fintype ι]
    (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hy0 : ∀ i, 0 ≤ y i)
    (hy1 : ∀ i, y i ≤ 1)
    (n k : ℕ) :
    0 ≤ hausdorffDiff k (moment w y) n := by
  rw [hausdorffDiff_moment]
  apply Finset.sum_nonneg
  intro i hi
  have hpowY : 0 ≤ (y i) ^ n := pow_nonneg (hy0 i) n
  have hOne : 0 ≤ 1 - y i := sub_nonneg.mpr (hy1 i)
  have hpowOne : 0 ≤ (1 - y i) ^ k := pow_nonneg hOne k
  exact mul_nonneg (mul_nonneg (hw i) hpowY) hpowOne

end XiHausdorff
end Millennium
