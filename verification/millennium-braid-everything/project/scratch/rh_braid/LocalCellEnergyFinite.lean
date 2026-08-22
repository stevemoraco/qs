import Mathlib

/-!
# Finite algebra behind the local-cell prime-energy discretization

These lemmas do not prove RH. They are the finite order-theoretic core used when
passing between a nonnegative sequence of local cell energies and its cumulative
partial sums.
-/

namespace RHProof
namespace LocalCellEnergy

/-- A nonnegative cell is bounded by the cumulative energy through that cell. -/
theorem cell_le_cumulative
    (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) :
    a N ≤ ∑ k in Finset.range (N + 1), a k := by
  rw [Finset.sum_range_succ]
  have hsum : 0 ≤ ∑ k in Finset.range N, a k := by
    exact Finset.sum_nonneg (fun k _ => ha k)
  linarith

/-- If every cell before `N` is at most `M`, the cumulative energy is at most `N*M`. -/
theorem cumulative_le_card_mul_bound
    (a : ℕ → ℝ)
    (N : ℕ)
    (M : ℝ)
    (hM : ∀ k < N, a k ≤ M) :
    (∑ k in Finset.range N, a k) ≤ (N : ℝ) * M := by
  calc
    (∑ k in Finset.range N, a k)
        ≤ ∑ _k in Finset.range N, M := by
          apply Finset.sum_le_sum
          intro k hk
          exact hM k (Finset.mem_range.mp hk)
    _ = (N : ℝ) * M := by simp [mul_comm]

/-- Finite block decomposition of cumulative energy. -/
theorem cumulative_succ
    (a : ℕ → ℝ)
    (N : ℕ) :
    (∑ k in Finset.range (N + 1), a k)
      = (∑ k in Finset.range N, a k) + a N := by
  simpa using Finset.sum_range_succ a N

end LocalCellEnergy
end RHProof
