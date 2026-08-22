import Mathlib

namespace YMJacobsenActivityFirewall

noncomputable section

def centerPlaquetteActivity (β : ℝ) : ℝ :=
  |Real.exp (-(3 * β / 2)) - 1|

theorem su3_center_real_defect :
    (3 : ℝ) - 3 * (-(1 : ℝ) / 2) = 9 / 2 := by
  norm_num

theorem center_activity_gt_half
    (β : ℝ)
    (hβ : (2 / 3 : ℝ) * Real.log 2 < β) :
    (1 / 2 : ℝ) < centerPlaquetteActivity β := by
  have harg : -(3 * β / 2) < -Real.log 2 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hexp : Real.exp (-(3 * β / 2)) < (1 / 2 : ℝ) := by
    calc
      Real.exp (-(3 * β / 2)) < Real.exp (-Real.log 2) :=
        Real.exp_lt_exp.mpr harg
      _ = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hnonpos : Real.exp (-(3 * β / 2)) - 1 ≤ 0 := by
    linarith
  rw [centerPlaquetteActivity, abs_of_nonpos hnonpos]
  linarith

theorem claimed_kp_ratio_exceeds_one
    (β : ℝ)
    (hβ : (2 / 3 : ℝ) * Real.log 2 < β) :
    1 < 12 * Real.exp 2 * centerPlaquetteActivity β := by
  have ha := center_activity_gt_half β hβ
  have he : 1 < Real.exp 2 := by
    simpa only [Real.exp_zero] using
      (Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2))
  have h6e : 6 < 6 * Real.exp 2 := by
    nlinarith
  have hscale :
      12 * Real.exp 2 * (1 / 2 : ℝ) <
        12 * Real.exp 2 * centerPlaquetteActivity β := by
    exact mul_lt_mul_of_pos_left ha (by positivity)
  nlinarith

theorem paper_kp_smallness_fails
    (β : ℝ)
    (hβ : (2 / 3 : ℝ) * Real.log 2 < β) :
    ¬ (12 * Real.exp 2 * centerPlaquetteActivity β < 1) := by
  have h := claimed_kp_ratio_exceeds_one β hβ
  linarith

theorem beta_630_is_beyond_half_activity_threshold :
    (2 / 3 : ℝ) * Real.log 2 < 630 := by
  have hlog : Real.log 2 < 2 := Real.log_lt_sub_one_of_pos (by norm_num)
  nlinarith

theorem beta_630_kp_smallness_fails :
    ¬ (12 * Real.exp 2 * centerPlaquetteActivity 630 < 1) := by
  exact paper_kp_smallness_fails 630 beta_630_is_beyond_half_activity_threshold

theorem claimed_weak_fit_counterexample :
    ¬ ((9 : ℝ) / ((1 : ℝ) / 100) +
        ((81 : ℝ) / 2) / (((1 : ℝ) / 100) ^ 2) ≤
      ((3 : ℝ) / 2) * ((1 : ℝ) / 100)) := by
  norm_num

theorem inverse_power_fit_impossible
    (x : ℝ)
    (hx : 0 < x)
    (hx1 : x ≤ 1) :
    ¬ ((9 : ℝ) / x + ((81 : ℝ) / 2) / x ^ 2 ≤
      ((3 : ℝ) / 2) * x) := by
  have h9x : 9 * x ≤ 9 := by nlinarith
  have h9 : (9 : ℝ) ≤ 9 / x := by
    exact (le_div_iff₀ hx).2 h9x
  have hsecond : 0 ≤ ((81 : ℝ) / 2) / x ^ 2 := by
    positivity
  intro hfit
  nlinarith

#print axioms su3_center_real_defect
#print axioms center_activity_gt_half
#print axioms claimed_kp_ratio_exceeds_one
#print axioms paper_kp_smallness_fails
#print axioms beta_630_is_beyond_half_activity_threshold
#print axioms beta_630_kp_smallness_fails
#print axioms claimed_weak_fit_counterexample
#print axioms inverse_power_fit_impossible

end

end YMJacobsenActivityFirewall
