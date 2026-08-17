import Mathlib

namespace Millennium.YangMills.FaizalShabirRelativeDefectFirewall

theorem exp_unit_gap_bound_fails
    (a Delta : ℝ)
    (ha : 0 < a)
    (hDelta : 1 < Delta) :
    Real.exp a < Real.exp (a * Delta) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

theorem exp_double_gap_counterexample
    (a : ℝ)
    (ha : 0 < a) :
    Real.exp a < Real.exp (a * 2) := by
  exact exp_unit_gap_bound_fails a 2 ha (by norm_num)

theorem gap_factor_times_transfer_radius
    (a Delta : ℝ) :
    Real.exp (a * Delta) * Real.exp (-(a * Delta)) = 1 := by
  rw [← Real.exp_add]
  simp

theorem gap_factor_is_reciprocal_radius
    (a Delta lambda : ℝ)
    (hlambda : lambda = Real.exp (-(a * Delta))) :
    Real.exp (a * Delta) * lambda = 1 := by
  subst lambda
  exact gap_factor_times_transfer_radius a Delta

theorem relative_defect_budget
    (radius defect theta : ℝ)
    (hdefect : defect ≤ theta * radius) :
    radius + defect ≤ (1 + theta) * radius := by
  linarith

theorem normalized_defect_from_relative_radius_bound
    (a Delta defect theta : ℝ)
    (hdefect : defect ≤ theta * Real.exp (-(a * Delta))) :
    Real.exp (a * Delta) * defect ≤ theta := by
  have hpos : 0 ≤ Real.exp (a * Delta) := le_of_lt (Real.exp_pos _)
  have hmul := mul_le_mul_of_nonneg_left hdefect hpos
  calc
    Real.exp (a * Delta) * defect
        ≤ Real.exp (a * Delta) * (theta * Real.exp (-(a * Delta))) := hmul
    _ = theta * (Real.exp (a * Delta) * Real.exp (-(a * Delta))) := by ring
    _ = theta := by rw [gap_factor_times_transfer_radius]; ring

#print axioms exp_unit_gap_bound_fails
#print axioms exp_double_gap_counterexample
#print axioms gap_factor_times_transfer_radius
#print axioms gap_factor_is_reciprocal_radius
#print axioms relative_defect_budget
#print axioms normalized_defect_from_relative_radius_bound

end Millennium.YangMills.FaizalShabirRelativeDefectFirewall
