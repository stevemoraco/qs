import Mathlib

namespace Millennium.YangMills.KirkV4GaussianCoreSizeFirewall

theorem kappa_below_eighth :
    (1 / 16 : ℝ) < 1 / 8 := by
  norm_num

theorem fixed_cross_operator_row_does_not_bound_second_trace_word (M : ℝ) :
    ∃ d : ℕ,
      (1 / 16 : ℝ) < 1 / 8 ∧
      M < (d : ℝ) * (1 / 16 : ℝ)^2 := by
  obtain ⟨d, hd⟩ := exists_nat_gt (256 * M)
  refine ⟨d, kappa_below_eighth, ?_⟩
  have hd' : 256 * M < (d : ℝ) := hd
  norm_num at ⊢
  nlinarith

theorem bounded_rank_controls_second_trace_word
    (rank kappa rankCap : ℝ)
    (hrank : rank ≤ rankCap) :
    rank * kappa^2 ≤ rankCap * kappa^2 := by
  exact mul_le_mul_of_nonneg_right hrank (sq_nonneg kappa)

theorem trace_cost_absorbed_by_support_reserve
    (traceCost support a c : ℝ)
    (htrace : traceCost ≤ c * support) :
    Real.exp (traceCost - a * support) ≤
      Real.exp (-(a - c) * support) := by
  apply Real.exp_le_exp.mpr
  linarith

end Millennium.YangMills.KirkV4GaussianCoreSizeFirewall
