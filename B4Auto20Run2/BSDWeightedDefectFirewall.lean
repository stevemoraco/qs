import Mathlib
namespace B4Auto20Run2

theorem bsd_two_weighted_defects_exact
    (d₀ d₁ w₀ w₁ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (hw₀ : 0 < w₀) (hw₁ : 0 < w₁)
    (hsum : w₀ * d₀ + w₁ * d₁ = 0) :
    d₀ = 0 ∧ d₁ = 0 := by
  have hp₀ : 0 ≤ w₀ * d₀ := mul_nonneg (le_of_lt hw₀) hd₀
  have hp₁ : 0 ≤ w₁ * d₁ := mul_nonneg (le_of_lt hw₁) hd₁
  have hz₀ : w₀ * d₀ = 0 := by linarith
  have hz₁ : w₁ * d₁ = 0 := by linarith
  constructor
  · rcases mul_eq_zero.mp hz₀ with h | h
    · exact (ne_of_gt hw₀ h).elim
    · exact h
  · rcases mul_eq_zero.mp hz₁ with h | h
    · exact (ne_of_gt hw₁ h).elim
    · exact h

theorem bsd_zero_weight_hides_positive_defect :
    let w₀ : ℝ := 0
    let w₁ : ℝ := 1
    let d₀ : ℝ := 1
    let d₁ : ℝ := 0
    0 ≤ d₀ ∧ 0 ≤ d₁ ∧ 0 ≤ w₀ ∧ 0 < w₁ ∧
      w₀ * d₀ + w₁ * d₁ = 0 ∧ d₀ ≠ 0 := by
  norm_num

#print axioms bsd_two_weighted_defects_exact
#print axioms bsd_zero_weight_hides_positive_defect
end B4Auto20Run2
