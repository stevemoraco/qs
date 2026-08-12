import Mathlib
namespace B4Auto20Run2

theorem rh_two_error_nonnegative_margin
    (m e₁ e₂ δ₁ δ₂ : ℝ)
    (he₁ : |e₁| ≤ δ₁) (he₂ : |e₂| ≤ δ₂)
    (hbudget : δ₁ + δ₂ ≤ m) :
    0 ≤ m + e₁ + e₂ := by
  have h₁ : -δ₁ ≤ e₁ := (abs_le.mp he₁).1
  have h₂ : -δ₂ ≤ e₂ := (abs_le.mp he₂).1
  linarith

theorem rh_two_error_strict_margin
    (m e₁ e₂ δ₁ δ₂ : ℝ)
    (he₁ : |e₁| ≤ δ₁) (he₂ : |e₂| ≤ δ₂)
    (hbudget : δ₁ + δ₂ < m) :
    0 < m + e₁ + e₂ := by
  have h₁ : -δ₁ ≤ e₁ := (abs_le.mp he₁).1
  have h₂ : -δ₂ ≤ e₂ := (abs_le.mp he₂).1
  linarith

theorem rh_budget_equality_can_kill_strict_sign :
    let m : ℝ := 1
    let e₁ : ℝ := -1
    let e₂ : ℝ := 0
    let δ₁ : ℝ := 1
    let δ₂ : ℝ := 0
    |e₁| ≤ δ₁ ∧ |e₂| ≤ δ₂ ∧ δ₁ + δ₂ = m ∧ m + e₁ + e₂ = 0 := by
  norm_num

#print axioms rh_two_error_nonnegative_margin
#print axioms rh_two_error_strict_margin
#print axioms rh_budget_equality_can_kill_strict_sign
end B4Auto20Run2
