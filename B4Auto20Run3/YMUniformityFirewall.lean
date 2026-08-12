import Mathlib

namespace B4Auto20Run3

theorem ym_two_positive_gaps_have_common_floor
    (g₁ g₂ : ℝ) (h₁ : 0 < g₁) (h₂ : 0 < g₂) :
    ∃ c : ℝ, 0 < c ∧ c ≤ g₁ ∧ c ≤ g₂ := by
  refine ⟨min g₁ g₂, ?_, min_le_left _ _, min_le_right _ _⟩
  exact lt_min h₁ h₂

theorem ym_pointwise_positive_gap_can_have_no_uniform_floor :
    (∀ a : ℝ, 0 < a → 0 < a) ∧
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → c ≤ a := by
  constructor
  · intro a ha
    exact ha
  · rintro ⟨c, hc, hfloor⟩
    have hhalf : 0 < c / 2 := by linarith
    have hle : c ≤ c / 2 := hfloor (c / 2) hhalf
    linarith

#print axioms B4Auto20Run3.ym_two_positive_gaps_have_common_floor
#print axioms B4Auto20Run3.ym_pointwise_positive_gap_can_have_no_uniform_floor

end B4Auto20Run3
