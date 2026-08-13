import Mathlib

namespace NSSidonLocalizationWindow

theorem beta_loc_window {α : ℝ} (hαlo : 2 < α) (hαhi : α < (5 : ℝ) / 2) :
    0 < 2 * (α - 1) / 3 ∧ 2 * (α - 1) / 3 < 1 := by
  constructor <;> nlinarith

theorem exists_shell_growth_window {β : ℝ} (hβpos : 0 < β) (hβlt : β < 1) :
    ∃ b : ℝ, 1 < b ∧ b * β < 1 := by
  refine ⟨(1 + 1 / β) / 2, ?_, ?_⟩
  · have hone_lt_inv : 1 < 1 / β := by
      rw [lt_div_iff₀ hβpos]
      nlinarith
    nlinarith
  · have hβne : β ≠ 0 := ne_of_gt hβpos
    have hcalc : ((1 + 1 / β) / 2) * β = (β + 1) / 2 := by
      field_simp [hβne]
      <;> ring
    rw [hcalc]
    nlinarith

theorem alpha_admits_shell_growth {α : ℝ} (hαlo : 2 < α) (hαhi : α < (5 : ℝ) / 2) :
    ∃ b : ℝ, 1 < b ∧ b * (2 * (α - 1) / 3) < 1 := by
  obtain ⟨hβpos, hβlt⟩ := beta_loc_window hαlo hαhi
  exact exists_shell_growth_window hβpos hβlt

#print axioms beta_loc_window
#print axioms exists_shell_growth_window
#print axioms alpha_admits_shell_growth

end NSSidonLocalizationWindow
