import Mathlib

/-!
# Kirk v4 support-reserve exponent repair

Finite real-analysis core for the support-versus-pivot-incidence estimate used
in Kirk v4, Theorem 6.10 / equation (HT5).

The source row carries a support exponent `m`.  If the destination row retains
its own positive support weight `a`, with `a < m`, then only the reserve
`m - a` remains available to pay separated-pivot incidence.  The original
source exponent `m` cannot simultaneously remain in the terminal decay factor.

This file proves the exact corrected exponent ledger.  It does not formalize
polymer activities, Peter--Weyl calculus, Yang--Mills theory, or a Clay result.
-/

namespace Millennium.YangMills.KirkV4SupportReserveExponentRepair

/-- Exact reserve ledger.  Suppose `n` selected pivots are separated strongly
enough that their reported support size `d` satisfies

`c * R * (n - 1) ≤ d`.

If the pivot charge `lambda` is no larger than the available support reserve
`(m-a) c R`, then the charged destination exponent is bounded by the reserve
rate, not by the original source rate `m`. -/
theorem charged_exponent_reserve
    (lambda a m c R n d : ℝ)
    (hma : a < m)
    (hn : 2 ≤ n)
    (hsep : c * R * (n - 1) ≤ d)
    (hcharge : lambda ≤ (m - a) * c * R) :
    lambda * n + a * d - m * d ≤
      2 * lambda - (m - a) * c * R := by
  have hk : 0 ≤ m - a := le_of_lt (sub_pos.mpr hma)
  have hsep' :
      (m - a) * (c * R * (n - 1)) ≤ (m - a) * d :=
    mul_le_mul_of_nonneg_left hsep hk
  have hcoef : lambda - (m - a) * c * R ≤ 0 :=
    sub_nonpos.mpr hcharge
  have hmul :
      (lambda - (m - a) * c * R) * n ≤
        (lambda - (m - a) * c * R) * 2 :=
    mul_le_mul_of_nonpos_left hn hcoef
  calc
    lambda * n + a * d - m * d
        = lambda * n - (m - a) * d := by ring
    _ ≤ lambda * n - (m - a) * (c * R * (n - 1)) := by
      linarith
    _ = (lambda - (m - a) * c * R) * n +
          (m - a) * c * R := by ring
    _ ≤ (lambda - (m - a) * c * R) * 2 +
          (m - a) * c * R := by
      linarith
    _ = 2 * lambda - (m - a) * c * R := by ring

/-- A single source-row term of size `exp (-m d)` becomes a destination-row
term of size `exp (-(m-a)d)` after retaining the positive target weight
`exp (a d)`. -/
theorem retained_weight_exact_identity (a m d : ℝ) :
    Real.exp (a * d) * Real.exp (-m * d) =
      Real.exp (-(m - a) * d) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The retained positive destination weight strictly slows the exponential
rate.  Thus a bound with the unchanged source exponent and unit constant is
already false on one saturating term. -/
theorem retained_positive_weight_slows_decay
    (a m c R : ℝ)
    (ha : 0 < a)
    (hc : 0 < c)
    (hR : 0 < R) :
    Real.exp (-m * (c * R)) <
      Real.exp (-(m - a) * (c * R)) := by
  apply Real.exp_lt_exp.mpr
  have hprod : 0 < a * (c * R) := mul_pos ha (mul_pos hc hR)
  nlinarith

/-- Exponent bookkeeping plus a source weighted bound gives the corrected
single-term transfer estimate. -/
theorem charged_weight_transfer
    (lambda a m c R n d v B : ℝ)
    (hma : a < m)
    (hn : 2 ≤ n)
    (hsep : c * R * (n - 1) ≤ d)
    (hcharge : lambda ≤ (m - a) * c * R)
    (hv : 0 ≤ v)
    (hB : Real.exp (m * d) * v ≤ B) :
    Real.exp (lambda * n + a * d) * v ≤
      Real.exp (2 * lambda - (m - a) * c * R) * B := by
  have hexponent :
      lambda * n + a * d - m * d ≤
        2 * lambda - (m - a) * c * R :=
    charged_exponent_reserve lambda a m c R n d hma hn hsep hcharge
  have hexp :
      Real.exp (lambda * n + a * d - m * d) ≤
        Real.exp (2 * lambda - (m - a) * c * R) :=
    Real.exp_le_exp.mpr hexponent
  have hsource0 : 0 ≤ Real.exp (m * d) * v :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hv
  calc
    Real.exp (lambda * n + a * d) * v
        = Real.exp (lambda * n + a * d - m * d) *
            (Real.exp (m * d) * v) := by
          have harg :
              lambda * n + a * d =
                (lambda * n + a * d - m * d) + m * d := by
            ring
          rw [harg, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (2 * lambda - (m - a) * c * R) * B := by
      exact mul_le_mul hexp hB hsource0
        (le_of_lt (Real.exp_pos _))

#print axioms charged_exponent_reserve
#print axioms retained_weight_exact_identity
#print axioms retained_positive_weight_slows_decay
#print axioms charged_weight_transfer

end Millennium.YangMills.KirkV4SupportReserveExponentRepair
