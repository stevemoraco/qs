import Mathlib

namespace NSLogisticDormantActivation

/-- Algebraic logistic profile after substituting `r = exp z`. -/
noncomputable def logisticRatio (r : ℝ) : ℝ := r / (1 + r)

/-- A nonnegative input gives a nonnegative logistic ratio. -/
theorem logistic_ratio_nonnegative
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ logisticRatio r := by
  unfold logisticRatio
  exact div_nonneg hr (by linarith)

/-- A strictly positive input gives a profile strictly below one. -/
theorem logistic_ratio_lt_one
    {r : ℝ} (hr : 0 < r) :
    logisticRatio r < 1 := by
  unfold logisticRatio
  have hden : 0 < 1 + r := by linarith
  exact (div_lt_iff₀ hden).2 (by linarith)

/-- Before the activation center (`r ≤ 1` in the exponential parametrization),
the logistic profile is no larger than its dormant exponential input. -/
theorem logistic_ratio_le_input
    {r : ℝ} (hr : 0 ≤ r) :
    logisticRatio r ≤ r := by
  unfold logisticRatio
  have hden : 0 < 1 + r := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg r]

/-- Exact complement identity. -/
theorem one_sub_logistic_ratio
    {r : ℝ} (hden : 1 + r ≠ 0) :
    1 - logisticRatio r = 1 / (1 + r) := by
  unfold logisticRatio
  field_simp [hden]
  ring

/-- Exact logistic derivative factor after the substitution `r = exp z`. -/
theorem logistic_product_identity
    {r : ℝ} (hden : 1 + r ≠ 0) :
    logisticRatio r * (1 - logisticRatio r) = r / (1 + r) ^ 2 := by
  unfold logisticRatio
  field_simp [hden]
  ring

/-- The logistic derivative factor is bounded by the profile itself. -/
theorem logistic_product_le_ratio (r : ℝ) :
    logisticRatio r * (1 - logisticRatio r) ≤ logisticRatio r := by
  nlinarith [sq_nonneg (logisticRatio r)]

/-- The universal one-quarter logistic derivative ceiling. -/
theorem logistic_product_le_quarter (r : ℝ) :
    logisticRatio r * (1 - logisticRatio r) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (2 * logisticRatio r - 1)]

/-- Scaling preserves the dormant exponential upper bound. -/
theorem scaled_logistic_tail_le_exponential
    {H r : ℝ}
    (hH : 0 ≤ H)
    (hr : 0 ≤ r) :
    H * logisticRatio r ≤ H * r := by
  exact mul_le_mul_of_nonneg_left (logistic_ratio_le_input hr) hH

/-- The algebraic relative-derivative budget for a scaled logistic activation. -/
theorem scaled_logistic_relative_rate
    {H tau r : ℝ}
    (hH : 0 ≤ H)
    (htau : 0 < tau) :
    (H / tau) *
        (logisticRatio r * (1 - logisticRatio r)) ≤
      (H * logisticRatio r) / tau := by
  have hscale : 0 ≤ H / tau := div_nonneg hH (le_of_lt htau)
  calc
    (H / tau) *
          (logisticRatio r * (1 - logisticRatio r)) ≤
        (H / tau) * logisticRatio r :=
      mul_le_mul_of_nonneg_left (logistic_product_le_ratio r) hscale
    _ = (H * logisticRatio r) / tau := by ring

/-- The scaled derivative factor has the exact universal quarter ceiling. -/
theorem scaled_logistic_quarter_rate
    {H tau r : ℝ}
    (hH : 0 ≤ H)
    (htau : 0 < tau) :
    (H / tau) *
        (logisticRatio r * (1 - logisticRatio r)) ≤
      H / (4 * tau) := by
  have hscale : 0 ≤ H / tau := div_nonneg hH (le_of_lt htau)
  calc
    (H / tau) *
          (logisticRatio r * (1 - logisticRatio r)) ≤
        (H / tau) * (1 / 4) :=
      mul_le_mul_of_nonneg_left (logistic_product_le_quarter r) hscale
    _ = H / (4 * tau) := by ring

/-- Exact center values: the logistic profile is one half and its derivative
factor is one quarter when the exponential input is one. -/
theorem logistic_center_values :
    logisticRatio 1 = 1 / 2 ∧
    logisticRatio 1 * (1 - logisticRatio 1) = 1 / 4 := by
  norm_num [logisticRatio]

/-- Exponential parametrization gives a strictly positive profile with no exact
zero-activation boundary. -/
theorem exponential_logistic_strictly_between
    (z : ℝ) :
    0 < logisticRatio (Real.exp z) ∧
    logisticRatio (Real.exp z) < 1 := by
  constructor
  · unfold logisticRatio
    exact div_pos (Real.exp_pos z) (by positivity)
  · exact logistic_ratio_lt_one (Real.exp_pos z)

/-- On the dormant side `z ≤ 0`, the logistic profile is bounded by `exp z`. -/
theorem exponential_logistic_dormant_bound
    {z : ℝ} :
    logisticRatio (Real.exp z) ≤ Real.exp z := by
  exact logistic_ratio_le_input (le_of_lt (Real.exp_pos z))

#print axioms logistic_ratio_nonnegative
#print axioms logistic_ratio_lt_one
#print axioms logistic_ratio_le_input
#print axioms one_sub_logistic_ratio
#print axioms logistic_product_identity
#print axioms logistic_product_le_ratio
#print axioms logistic_product_le_quarter
#print axioms scaled_logistic_tail_le_exponential
#print axioms scaled_logistic_relative_rate
#print axioms scaled_logistic_quarter_rate
#print axioms logistic_center_values
#print axioms exponential_logistic_strictly_between
#print axioms exponential_logistic_dormant_bound

end NSLogisticDormantActivation
