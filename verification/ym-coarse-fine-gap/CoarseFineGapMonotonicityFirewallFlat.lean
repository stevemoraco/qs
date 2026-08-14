import Mathlib

namespace Millennium.YangMills

theorem fine_lower_bound_lifts_to_coarse
    (fine coarse μ : ℝ)
    (hmono : fine ≤ coarse)
    (hfine : μ ≤ fine) :
    μ ≤ coarse :=
  le_trans hfine hmono

theorem coarse_lower_bound_does_not_descend :
    ∃ fine coarse μ : ℝ,
      fine ≤ coarse ∧ μ ≤ coarse ∧ ¬ μ ≤ fine := by
  refine ⟨0, 2, 1, ?_⟩
  norm_num

theorem coarse_lower_bound_descends_with_loss
    (fine coarse μ ε : ℝ)
    (hcoarse : μ ≤ coarse)
    (hback : coarse ≤ fine + ε) :
    μ - ε ≤ fine := by
  linarith

#print axioms fine_lower_bound_lifts_to_coarse
#print axioms coarse_lower_bound_does_not_descend
#print axioms coarse_lower_bound_descends_with_loss

end Millennium.YangMills
