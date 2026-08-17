import Mathlib

/-!
# Faizal--Shabir relative transfer-defect firewall

Finite real-analysis facts behind the physical-unit defect audit of the
Faizal--Shabir transfer-gap recursion.

The manuscript's Theorem 5.4 reaches a loss term proportional to
`exp (a_next * Delta) * defect / a_next` and then bounds the exponential
factor by `exp a_next` using only `Delta >= 0`. That inference is false:
for positive spacing and any `Delta > 1`, the inequality goes in the
opposite direction.

The correct multiplicative factor is the reciprocal transfer radius when
`lambda = exp (-a * Delta)`. Thus an additive operator defect must be
controlled relative to the current transfer radius (or inside an invariant
normalized-gap tube), not merely by an absolute summability estimate.

The final declarations record the exact same-base exponent race between a
physical transfer radius `exp (-m*a0*b^(k+1))` and a collar tail
`exp (-c*r0*b^k)`. In that matched-base case, the normalized exponent is
`b^k * (m*a0*b - c*r0)`, so the collar wins pointwise only after the missing
coefficient comparison `m*a0*b <= c*r0` is supplied.

This file formalizes only finite scalar identities and inequalities. It does
not formalize transfer operators, OS Hilbert spaces, Yang--Mills theory, or a
Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirRelativeDefectFirewall

/-- Positive spacing and a gap larger than one make the manuscript's claimed
`exp (a*Delta) <= exp a` bound fail in the strict opposite direction. -/
theorem exp_unit_gap_bound_fails
    (a Delta : ℝ)
    (ha : 0 < a)
    (hDelta : 1 < Delta) :
    Real.exp a < Real.exp (a * Delta) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- A concrete valid hostile value: `Delta = 2` already violates the claimed
unit-gap exponential bound for every positive spacing. -/
theorem exp_double_gap_counterexample
    (a : ℝ)
    (ha : 0 < a) :
    Real.exp a < Real.exp (a * 2) := by
  exact exp_unit_gap_bound_fails a 2 ha (by norm_num)

/-- The physical gap exponential is exactly reciprocal to its transfer radius.
This is the load-bearing relative-error normalization. -/
theorem gap_factor_times_transfer_radius
    (a Delta : ℝ) :
    Real.exp (a * Delta) * Real.exp (-(a * Delta)) = 1 := by
  rw [← Real.exp_add]
  simp

/-- If `lambda` is the transfer radius `exp (-a*Delta)`, multiplying by the
physical gap factor cancels it exactly. -/
theorem gap_factor_is_reciprocal_radius
    (a Delta lambda : ℝ)
    (hlambda : lambda = Real.exp (-(a * Delta))) :
    Real.exp (a * Delta) * lambda = 1 := by
  subst lambda
  exact gap_factor_times_transfer_radius a Delta

/-- A defect controlled by a fixed fraction of the transfer radius remains a
fixed relative perturbation. -/
theorem relative_defect_budget
    (radius defect theta : ℝ)
    (hdefect : defect ≤ theta * radius) :
    radius + defect ≤ (1 + theta) * radius := by
  linarith

/-- If the additive defect is bounded by `theta * exp (-a*Delta)`, then after
multiplication by the physical gap factor it costs at most `theta`. -/
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

/-- In the matched-base case `a_(k+1)=a0*b^(k+1)` and
`R_k=r0*b^k`, the exponent of the physical-normalized collar tail factors
exactly into one power `b^k` times a fixed coefficient race. -/
theorem same_base_relative_tail_exponent
    (m a0 b c r0 : ℝ) (k : ℕ) :
    m * (a0 * b ^ (k + 1)) - c * (r0 * b ^ k)
      = b ^ k * (m * a0 * b - c * r0) := by
  rw [pow_succ]
  ring

/-- If the collar-decay coefficient beats the physical transfer coefficient
in the matched-base case, the normalized exponential tail is at most one at
every scale. This is the finite scalar shadow of the missing relative-tail
comparison theorem. -/
theorem same_base_relative_tail_le_one
    (m a0 b c r0 : ℝ) (k : ℕ)
    (hb : 0 ≤ b)
    (hmargin : m * a0 * b ≤ c * r0) :
    Real.exp (m * (a0 * b ^ (k + 1)) - c * (r0 * b ^ k)) ≤ 1 := by
  have hnonpos :
      m * (a0 * b ^ (k + 1)) - c * (r0 * b ^ k) ≤ 0 := by
    rw [same_base_relative_tail_exponent]
    exact mul_nonpos_of_nonneg_of_nonpos
      (pow_nonneg hb k) (sub_nonpos.mpr hmargin)
  have h := Real.exp_le_exp.mpr hnonpos
  simpa using h

#print axioms exp_unit_gap_bound_fails
#print axioms exp_double_gap_counterexample
#print axioms gap_factor_times_transfer_radius
#print axioms gap_factor_is_reciprocal_radius
#print axioms relative_defect_budget
#print axioms normalized_defect_from_relative_radius_bound
#print axioms same_base_relative_tail_exponent
#print axioms same_base_relative_tail_le_one

end Millennium.YangMills.FaizalShabirRelativeDefectFirewall
