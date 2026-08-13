import Mathlib

namespace ProfileResidualFinite

theorem residual_square_scaling
    (scale m3 m4 : ℝ) :
    scale ^ 2 * m4 - (scale * m3) ^ 2 =
      scale ^ 2 * (m4 - m3 ^ 2) := by
  ring

theorem positive_defect_survives_scaling
    (scaleSq defect : ℝ)
    (hscale : 0 < scaleSq)
    (hdefect : 0 < defect) :
    0 < scaleSq * defect := by
  exact mul_pos hscale hdefect

theorem residual_ratio_scale_cancels
    (scaleSq defect selectedSq : ℝ)
    (hscale : scaleSq ≠ 0)
    (hselected : selectedSq ≠ 0) :
    (scaleSq * defect) / (scaleSq * selectedSq) =
      defect / selectedSq := by
  field_simp

theorem idempotent_value_firewall
    (x m : ℝ)
    (h : x ^ 2 = m * x) :
    x = 0 ∨ x = m := by
  have hfactor : x * (x - m) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hx | hxm
  · exact Or.inl hx
  · right
    linarith

theorem midpoint_breaks_idempotence
    (m : ℝ)
    (hm : m ≠ 0) :
    (m / 2) ^ 2 ≠ m * (m / 2) := by
  intro h
  have hvalues := idempotent_value_firewall (m / 2) m h
  rcases hvalues with hzero | hfull
  · apply hm
    linarith
  · apply hm
    linarith

inductive StatementKind where
  | selected
  | complete
  deriving DecidableEq

theorem selected_ne_complete :
    StatementKind.selected ≠ StatementKind.complete := by
  decide

#print axioms residual_square_scaling
#print axioms positive_defect_survives_scaling
#print axioms residual_ratio_scale_cancels
#print axioms idempotent_value_firewall
#print axioms midpoint_breaks_idempotence
#print axioms selected_ne_complete

end ProfileResidualFinite
