import Mathlib

namespace B4.Run22.RH

theorem banker_two_interval_trace_budget {x₁ x₂ E₁ E₂ w₁ w₂ c : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (h₁ : x₁ ^ 2 ≤ 2 * E₁ + c) (h₂ : x₂ ^ 2 ≤ 2 * E₂ + c) :
    w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2 ≤
      2 * (w₁ * E₁ + w₂ * E₂) + c * (w₁ + w₂) := by
  have h₁' := mul_le_mul_of_nonneg_left h₁ hw₁
  have h₂' := mul_le_mul_of_nonneg_left h₂ hw₂
  nlinarith

theorem critic_trace_constant_accumulates :
    (1 : ℝ) ^ 2 ≤ 2 * 0 + 1 ∧
    (1 : ℝ) ^ 2 ≤ 2 * 0 + 1 ∧
    ¬ ((1 : ℝ) * 1 ^ 2 + 1 * 1 ^ 2 ≤ 1) := by
  norm_num

theorem cleaner_trace_budget_with_weight_cap {x₁ x₂ E₁ E₂ w₁ w₂ c W : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hc : 0 ≤ c)
    (h₁ : x₁ ^ 2 ≤ 2 * E₁ + c) (h₂ : x₂ ^ 2 ≤ 2 * E₂ + c)
    (hW : w₁ + w₂ ≤ W) :
    w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2 ≤
      2 * (w₁ * E₁ + w₂ * E₂) + c * W := by
  have hbase := banker_two_interval_trace_budget hw₁ hw₂ h₁ h₂
  have hcap := mul_le_mul_of_nonneg_left hW hc
  nlinarith

#print axioms banker_two_interval_trace_budget
#print axioms critic_trace_constant_accumulates
#print axioms cleaner_trace_budget_with_weight_cap

end B4.Run22.RH
