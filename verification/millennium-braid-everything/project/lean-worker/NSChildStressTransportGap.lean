import Mathlib

namespace NSChildStressTransportGap

/-- Factorization of the coefficient multiplying `beta-alpha` in the parent-transport gap. -/
theorem transport_coeff_factor (b : ℝ) :
    2*b - 1 - 1/b = ((b-1)*(2*b+1))/b := by
  field_simp
  ring

/-- In the Palasek physical window, the parent-transport coefficient lies strictly between 0 and 1. -/
theorem transport_coeff_between_zero_one
    {b : ℝ} (hb1 : 1 < b) (hb5 : b < (5:ℝ)/4) :
    0 < 2*b - 1 - 1/b ∧ 2*b - 1 - 1/b < 1 := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb1
  constructor
  · rw [transport_coeff_factor]
    exact div_pos (mul_pos (sub_pos.mpr hb1) (by nlinarith)) hbpos
  · apply (sub_lt_iff_lt_add).2
    have hquad : 2*b^2 - 2*b - 1 < 0 := by
      nlinarith [sq_nonneg (b - (5:ℝ)/4)]
    apply (lt_div_iff₀ hbpos).2
    nlinarith

/-- The child high-high stress exponent strictly dominates the parent-transport exponent. -/
theorem transport_gap_pos
    {alpha beta b : ℝ}
    (ha2 : 2 < alpha)
    (ha5 : alpha ≤ (5:ℝ)/2)
    (hb1 : 1 < b)
    (hba : b < alpha/2)
    (hbeta : 2*b < beta)
    (hbetaa : beta < alpha) :
    0 < alpha - 1 + (beta-alpha)*(2*b - 1 - 1/b) := by
  have hb5 : b < (5:ℝ)/4 := by nlinarith
  obtain ⟨hc0, hc1⟩ := transport_coeff_between_zero_one hb1 hb5
  have hdneg : beta - alpha < 0 := sub_neg.mpr hbetaa
  have hdlow : 2*b - alpha < beta - alpha := by nlinarith
  have halpha2b0 : 0 < alpha - 2*b := by nlinarith
  have halpha2bhalf : alpha - 2*b < (1:ℝ)/2 := by nlinarith
  have hmul : -(alpha - 2*b) < (beta-alpha)*(2*b - 1 - 1/b) := by
    have h1 : (2*b-alpha)*(2*b - 1 - 1/b) < (beta-alpha)*(2*b - 1 - 1/b) :=
      mul_lt_mul_of_pos_right hdlow hc0
    have h2 : -(alpha - 2*b) < (2*b-alpha)*(2*b - 1 - 1/b) := by
      have := mul_lt_mul_of_neg_left hc1 (by nlinarith : 2*b-alpha < 0)
      nlinarith
    linarith
  nlinarith

#print axioms transport_coeff_factor
#print axioms transport_coeff_between_zero_one
#print axioms transport_gap_pos

end NSChildStressTransportGap
