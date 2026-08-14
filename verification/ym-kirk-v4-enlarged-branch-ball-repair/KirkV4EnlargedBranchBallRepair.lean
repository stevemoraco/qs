import Mathlib

namespace Millennium.YangMills

theorem enlarged_branch_ball_admission
    (J A : ℝ)
    (hJ : 0 < J)
    (hA : A ≤ 1 + 1 / (2 * J)) :
    J * A - 1 < J := by
  have hJ0 : 0 ≤ J := le_of_lt hJ
  have hmul : J * A ≤ J * (1 + 1 / (2 * J)) :=
    mul_le_mul_of_nonneg_left hA hJ0
  have hne : J ≠ 0 := ne_of_gt hJ
  have hcalc : J * (1 + 1 / (2 * J)) - 1 = J - (1 / 2 : ℝ) := by
    field_simp [hne]
    ring
  calc
    J * A - 1 ≤ J * (1 + 1 / (2 * J)) - 1 := sub_le_sub_right hmul 1
    _ = J - (1 / 2 : ℝ) := hcalc
    _ < J := by norm_num

theorem positive_junction_has_enlarged_ball_margin
    (J : ℝ)
    (hJ : 0 < J) :
    ∃ B δ : ℝ,
      0 < B ∧
      0 < δ ∧
      (∀ A : ℝ, A ≤ 1 + δ → J * A - 1 < B) := by
  refine ⟨J, 1 / (2 * J), hJ, ?_, ?_⟩
  · positivity
  · intro A hA
    exact enlarged_branch_ball_admission J A hJ hA

theorem enlarged_ball_has_strict_baseline_room
    (J : ℝ) :
    J - 1 < J := by
  linarith

#print axioms enlarged_branch_ball_admission
#print axioms positive_junction_has_enlarged_ball_margin
#print axioms enlarged_ball_has_strict_baseline_room

end Millennium.YangMills
