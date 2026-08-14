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

theorem affine_contractive_step_preserves_ball
    (q C M x : ℝ)
    (hq : 0 ≤ q)
    (hx : x ≤ M)
    (hC : C ≤ (1 - q) * M) :
    q * x + C ≤ M := by
  have hqx : q * x ≤ q * M := mul_le_mul_of_nonneg_left hx hq
  calc
    q * x + C ≤ q * M + C := by
      simpa [add_comm] using add_le_add_right hqx C
    _ ≤ q * M + (1 - q) * M := by
      simpa [add_comm] using add_le_add_left hC (q * M)
    _ = M := by ring

theorem affine_contractive_sequence_bounded
    (x : ℕ → ℝ)
    (q C M : ℝ)
    (hq : 0 ≤ q)
    (hinit : x 0 ≤ M)
    (hrec : ∀ n : ℕ, x (n + 1) ≤ q * x n + C)
    (hC : C ≤ (1 - q) * M) :
    ∀ n : ℕ, x n ≤ M := by
  intro n
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
      have hstep := hrec n
      have hbound := affine_contractive_step_preserves_ball q C M (x n) hq ih hC
      exact le_trans hstep hbound

theorem strict_contraction_has_forcing_ball
    (q C : ℝ)
    (hq1 : q < 1)
    (hC0 : 0 ≤ C) :
    ∃ M : ℝ, 0 < M ∧ C ≤ (1 - q) * M := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have hd0 : 0 ≤ 1 - q := le_of_lt hd
  let M : ℝ := C / (1 - q) + 1
  have hM : 0 < M := by
    dsimp [M]
    have hdiv : 0 ≤ C / (1 - q) := div_nonneg hC0 hd0
    linarith
  refine ⟨M, hM, ?_⟩
  have hne : 1 - q ≠ 0 := ne_of_gt hd
  have hcalc : (1 - q) * M = C + (1 - q) := by
    dsimp [M]
    field_simp [hne]
  rw [hcalc]
  linarith

#print axioms enlarged_branch_ball_admission
#print axioms positive_junction_has_enlarged_ball_margin
#print axioms enlarged_ball_has_strict_baseline_room
#print axioms affine_contractive_step_preserves_ball
#print axioms affine_contractive_sequence_bounded
#print axioms strict_contraction_has_forcing_ball

end Millennium.YangMills
