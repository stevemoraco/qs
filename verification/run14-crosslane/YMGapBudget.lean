import Mathlib

namespace MillenniumRun14

/-- Iterating one-step gap losses gives the exact cumulative defect budget. -/
theorem ym_cumulative_gap_budget
    (m d : ℕ → ℝ)
    (hstep : ∀ k, m (k + 1) ≥ m k - d k) :
    ∀ n, m n ≥ m 0 - ∑ k ∈ Finset.range n, d k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep n
      rw [Finset.sum_range_succ]
      norm_num at hs ⊢
      linarith

#print axioms ym_cumulative_gap_budget

end MillenniumRun14
