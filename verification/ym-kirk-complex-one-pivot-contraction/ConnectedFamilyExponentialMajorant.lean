import Mathlib

namespace Millennium.YangMills

/-!
# Connected-family exponential majorant margin

Finite scalar bridge for the activity-only connected-family recursion used in
the complex compact-denominator repair.

If a rooted hypergraph generating function `Xi` is bounded by `log 2` on the
unit branch ball, then `exp Xi - 1` maps that scalar range into `[0,1]`. If its
slope is bounded by `eps1` with `2*eps1 < 1`, the corresponding exponential
slope bound is strictly below one because `exp Xi <= 2`.

This file proves only that scalar admission arithmetic. It does not prove the
Kirk connected-family majorant, a Kotecky--Preiss theorem, the complex compact
denominator, Theorem 6.43, OS reconstruction, Yang--Mills mass gap, or a Clay
theorem.
-/

theorem exp_sub_one_le_one_of_le_log_two
    (x : ℝ)
    (hx : x ≤ Real.log 2) :
    Real.exp x - 1 ≤ 1 := by
  have hexp : Real.exp x ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hx
  have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
    rw [Real.exp_log]
    norm_num
  rw [htwo] at hexp
  linarith

theorem exponential_branch_slope_lt_one
    (x eps1 : ℝ)
    (hx : x ≤ Real.log 2)
    (heps1 : 0 ≤ eps1)
    (hsmall : 2 * eps1 < 1) :
    Real.exp x * eps1 < 1 := by
  have hexp : Real.exp x ≤ (2 : ℝ) := by
    have h := Real.exp_le_exp.mpr hx
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  have hmul : Real.exp x * eps1 ≤ 2 * eps1 :=
    mul_le_mul_of_nonneg_right hexp heps1
  exact lt_of_le_of_lt hmul hsmall

theorem connected_family_exponential_admission
    (x eps1 : ℝ)
    (hx : x ≤ Real.log 2)
    (heps1 : 0 ≤ eps1)
    (hsmall : 2 * eps1 < 1) :
    Real.exp x - 1 ≤ 1 ∧ Real.exp x * eps1 < 1 := by
  exact ⟨exp_sub_one_le_one_of_le_log_two x hx,
    exponential_branch_slope_lt_one x eps1 hx heps1 hsmall⟩

#print axioms exp_sub_one_le_one_of_le_log_two
#print axioms exponential_branch_slope_lt_one
#print axioms connected_family_exponential_admission

end Millennium.YangMills
