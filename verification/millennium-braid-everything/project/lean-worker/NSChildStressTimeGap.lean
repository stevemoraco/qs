import Mathlib

namespace NSChildStressTimeGap

/-- Exact factorization of the child-stress versus parent activation-time exponent gap. -/
theorem time_gap_factorization (alpha beta b : ℝ) :
    (alpha + 2*b*(beta-alpha)) - (beta/b + beta - alpha)
      = ((b-1)/b) * ((2*b+1)*beta - 2*alpha*b) := by
  field_simp
  ring

/-- In the physical Palasek window, the factor controlling the time-budget gap is positive. -/
theorem inner_factor_pos
    {alpha beta b : ℝ}
    (hb : 1 < b)
    (ha : alpha ≤ (5:ℝ)/2)
    (hbeta : 2*b < beta) :
    0 < (2*b+1)*beta - 2*alpha*b := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  have hcoef : 0 < 2*b + 1 := by nlinarith
  have h1 : (2*b+1)*(2*b) < (2*b+1)*beta :=
    (mul_lt_mul_of_pos_left hbeta hcoef)
  have halpha : 2*alpha*b ≤ 5*b := by
    nlinarith
  have hbase : 5*b < (2*b+1)*(2*b) := by
    nlinarith
  nlinarith

/-- The child high-high stress exponent strictly dominates the parent activation-time residual exponent. -/
theorem time_gap_pos
    {alpha beta b : ℝ}
    (hb : 1 < b)
    (ha : alpha ≤ (5:ℝ)/2)
    (hbeta : 2*b < beta) :
    0 < (alpha + 2*b*(beta-alpha)) - (beta/b + beta - alpha) := by
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  have hfrac : 0 < (b-1)/b := div_pos (sub_pos.mpr hb) hbpos
  have hin := inner_factor_pos hb ha hbeta
  rw [time_gap_factorization]
  exact mul_pos hfrac hin

#print axioms time_gap_factorization
#print axioms inner_factor_pos
#print axioms time_gap_pos

end NSChildStressTimeGap
