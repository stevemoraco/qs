import Mathlib

namespace Millennium.YangMills

/-!
# Exponential rooted-family row to KP budget

Finite scalar bridge for the repaired Kirk-v4 compact denominator architecture.

If a first-incidence connected-family majorant gives a rooted row bounded by
`exp eps - 1`, then the standard Kotecky--Preiss per-pivot budget `alpha` is
met as soon as `eps <= log (1 + alpha)`.

This file proves only that scalar conversion.  It does not prove Kirk's
complex promoted activity row, the connected-family first-incidence majorant,
the Kotecky--Preiss theorem, Theorem 6.43, OS reconstruction, Yang--Mills mass
gap, Lambda normalization, or a Clay theorem.
-/

/-- If `eps` is below `log (1 + alpha)`, with `alpha >= 0`, then the
exponential rooted-family majorant `exp eps - 1` fits inside the KP budget
`alpha`. -/
theorem exp_sub_one_le_kp_budget
    (eps alpha : ℝ)
    (halpha : 0 ≤ alpha)
    (heps : eps ≤ Real.log (1 + alpha)) :
    Real.exp eps - 1 ≤ alpha := by
  have hpos : 0 < 1 + alpha := by linarith
  have h := Real.exp_le_exp.mpr heps
  rw [Real.exp_log hpos] at h
  linarith

/-- A paired sufficient condition used in the connected-family repair: a
single `eps` bound can keep the rooted-family row both inside the unit branch
ball and below a prescribed KP budget. -/
theorem exp_sub_one_le_unit_and_kp_budget
    (eps alpha : ℝ)
    (halpha : 0 ≤ alpha)
    (hunit : eps ≤ Real.log 2)
    (hkp : eps ≤ Real.log (1 + alpha)) :
    Real.exp eps - 1 ≤ 1 ∧ Real.exp eps - 1 ≤ alpha := by
  constructor
  · have h := Real.exp_le_exp.mpr hunit
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  · exact exp_sub_one_le_kp_budget eps alpha halpha hkp

#print axioms exp_sub_one_le_kp_budget
#print axioms exp_sub_one_le_unit_and_kp_budget

end Millennium.YangMills
