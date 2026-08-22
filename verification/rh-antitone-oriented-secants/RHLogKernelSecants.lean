import RHAntitoneOrientedSecants
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# The logarithmic kernel in the signed Robin--Johnston secant estimate

This file specializes the generic oriented-secant theorem to

`q(x) = 1 / (x * (log x)^2)`

on `(1,infinity)`.  It proves antitonicity, the exact antiderivative identity,
and the resulting signed one-cell bound.  Midpoint convexity and the global RH
sign theorem remain separate.
-/

open MeasureTheory Set
open scoped Interval

namespace RHLogKernelSecants

/-- The positive logarithmic secant kernel. -/
def logKernel (x : ℝ) : ℝ := 1 / (x * Real.log x ^ 2)

/-- The logarithmic kernel is antitone on `(1,infinity)`. -/
theorem logKernel_antitoneOn_Ioi_one :
    AntitoneOn logKernel (Ioi (1 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hly : 0 < Real.log y := Real.log_pos hy
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hsq : Real.log x ^ 2 ≤ Real.log y ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hlog)
      (add_nonneg hlx.le hly.le)
    nlinarith
  have hden : x * Real.log x ^ 2 ≤ y * Real.log y ^ 2 :=
    mul_le_mul hxy hsq (sq_nonneg (Real.log x)) hy0.le
  have hdenpos : 0 < x * Real.log x ^ 2 :=
    mul_pos hx0 (pow_pos hlx 2)
  exact one_div_le_one_div_of_le hdenpos hden

/-- Restriction of logarithmic-kernel antitonicity to any unordered interval
whose endpoints exceed one. -/
theorem logKernel_antitoneOn_uIcc
    (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    AntitoneOn logKernel (uIcc a b) := by
  apply logKernel_antitoneOn_Ioi_one.mono
  intro x hx
  change x ∈ Icc (min a b) (max a b) at hx
  exact (lt_min ha hb).trans_le hx.1

/-- Derivative of `-1/log x` in the positive domain. -/
theorem hasDerivAt_neg_inv_log_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => -(Real.log y)⁻¹) (logKernel x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hxm1 : x ≠ -1 := by linarith
  have h := (Real.hasDerivAt_inv_log hx0 hx1 hxm1).neg
  simpa [logKernel, one_div, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using h

/-- Exact oriented antiderivative identity for the logarithmic kernel. -/
theorem integral_logKernel
    (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    (∫ x in a..b, logKernel x) =
      (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hq : AntitoneOn logKernel (uIcc a b) :=
    logKernel_antitoneOn_uIcc a b ha hb
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -(Real.log y)⁻¹) (logKernel x) x := by
    intro x hx
    apply hasDerivAt_neg_inv_log_of_one_lt
    change x ∈ Icc (min a b) (max a b) at hx
    exact (lt_min ha hb).trans_le hx.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hq.intervalIntegrable
  simpa using h

/-- The specific signed secant theorem in inverse-log coordinates. -/
theorem logarithmic_signed_secant
    (p m L buffer robin : ℝ)
    (hp : 1 < p)
    (hm : 1 < m)
    (hL : L = Real.log p)
    (hidentity : robin = buffer +
      L * ((Real.log m)⁻¹ - (Real.log p)⁻¹)) :
    buffer + (L * (p - m)) * logKernel p ≤ robin ∧
      robin ≤ buffer + (L * (p - m)) * logKernel m := by
  have hLnonneg : 0 ≤ L := by
    rw [hL]
    exact (Real.log_pos hp).le
  have hq : AntitoneOn logKernel (uIcc m p) :=
    logKernel_antitoneOn_uIcc m p hm hp
  have hint := integral_logKernel m p hm hp
  have hidentity' : robin = buffer + L * (∫ u in m..p, logKernel u) := by
    rw [hint]
    exact hidentity
  exact RHAntitoneOrientedSecants.signed_secant_transfer
    logKernel p m L buffer robin hLnonneg hq hidentity'

/-- The signed theorem for a cell whose Robin and buffer terms share an
arbitrary common integral `cellIntegral`. -/
theorem logarithmic_cell_signed_secant
    (p m L cellIntegral : ℝ)
    (hp : 1 < p)
    (hm : 1 < m)
    (hL : L = Real.log p) :
    (cellIntegral - L * (Real.log m)⁻¹) +
        (L * (p - m)) * logKernel p ≤ cellIntegral - 1 ∧
      cellIntegral - 1 ≤
        (cellIntegral - L * (Real.log m)⁻¹) +
          (L * (p - m)) * logKernel m := by
  have hlogp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  have hone : L * (Real.log p)⁻¹ = 1 := by
    rw [hL]
    exact mul_inv_cancel₀ hlogp
  apply logarithmic_signed_secant p m L
    (cellIntegral - L * (Real.log m)⁻¹) (cellIntegral - 1)
    hp hm hL
  calc
    cellIntegral - 1 = cellIntegral - L * (Real.log p)⁻¹ := by rw [hone]
    _ = (cellIntegral - L * (Real.log m)⁻¹) +
        L * ((Real.log m)⁻¹ - (Real.log p)⁻¹) := by ring

end RHLogKernelSecants

#print axioms RHLogKernelSecants.logKernel_antitoneOn_Ioi_one
#print axioms RHLogKernelSecants.logKernel_antitoneOn_uIcc
#print axioms RHLogKernelSecants.hasDerivAt_neg_inv_log_of_one_lt
#print axioms RHLogKernelSecants.integral_logKernel
#print axioms RHLogKernelSecants.logarithmic_signed_secant
#print axioms RHLogKernelSecants.logarithmic_cell_signed_secant
