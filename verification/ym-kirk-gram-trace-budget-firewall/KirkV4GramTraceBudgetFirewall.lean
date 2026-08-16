import Mathlib

namespace Millennium.YangMills.KirkV4GramTraceBudgetFirewall

theorem quarter_operator_admission :
    2 * (1 / 4 : ℝ) < 1 := by
  norm_num

theorem fixed_operator_budget_does_not_bound_trace_proxy (M : ℝ) :
    ∃ d : ℕ,
      2 * (1 / 4 : ℝ) < 1 ∧
      M < (d : ℝ) * (1 / 4 : ℝ) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (4 * M)
  refine ⟨d, quarter_operator_admission, ?_⟩
  have hd' : 4 * M < (d : ℝ) := hd
  nlinarith

theorem trace_budget_from_support_budget
    {ι : Type*} [Fintype ι]
    (traceCost support : ι → ℝ) (c : ℝ)
    (hlocal : ∀ i, traceCost i ≤ c * support i) :
    ∑ i, traceCost i ≤ c * ∑ i, support i := by
  calc
    ∑ i, traceCost i ≤ ∑ i, c * support i := by
      exact Finset.sum_le_sum fun i _ => hlocal i
    _ = c * ∑ i, support i := by
      rw [Finset.mul_sum]

end Millennium.YangMills.KirkV4GramTraceBudgetFirewall
