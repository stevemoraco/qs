import Mathlib

/-!
# Faizal--Shabir connected-log exponential recertification

Finite real-exponential majorants for the load-bearing repair gate
`YM-FS-CONNECTED-LOG-TAIL-TO-OS-SCHUR`.

The analytic operator theorem still has to place the connected logarithm and
its collar tail in one regulator/volume/scale-uniform submultiplicative Schur
(or stronger Banach-algebra) norm.  Once that is supplied, the standard
noncommutative exponential perturbation estimate shows that exponentiation
changes only a bounded prefactor, not the tail exponent.

This file kernelizes only the scalar majorant mechanism:

* `exp x - 1 <= x exp x` for `x >= 0`;
* adding a nonnegative tail to a bounded logarithm changes the exponential by
  at most `tail * exp(baseLog + tail)`;
* if `tail <= C * decay`, with `0 <= decay <= 1`, then exponentiation preserves
  the same `decay` factor with the uniform prefactor `C * exp(M + C)`.

It does not formalize polymer activities, connected logarithms, Schur kernels,
operator exponentials, Osterwalder--Schrader transfer operators, Yang--Mills,
a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirConnectedLogExponentialRecertification

/-- Elementary exponential remainder bound used as the scalar majorant for the
Banach-algebra exponential perturbation estimate. -/
theorem exp_sub_one_le_mul_exp
    (x : ℝ)
    (hx : 0 ≤ x) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hbase : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  have hone : 1 - Real.exp (-x) ≤ x := by
    linarith
  have hexp_nonneg : 0 ≤ Real.exp x := le_of_lt (Real.exp_pos x)
  have hmul :
      (1 - Real.exp (-x)) * Real.exp x ≤ x * Real.exp x :=
    mul_le_mul_of_nonneg_right hone hexp_nonneg
  have hinv : Real.exp (-x) * Real.exp x = 1 := by
    calc
      Real.exp (-x) * Real.exp x = Real.exp (-x + x) := by
        rw [← Real.exp_add]
      _ = 1 := by simp
  calc
    Real.exp x - 1 = (1 - Real.exp (-x)) * Real.exp x := by
      rw [sub_mul, one_mul, hinv]
    _ ≤ x * Real.exp x := hmul

/-- A nonnegative additive logarithmic tail changes the scalar exponential by
at most `tail * exp(baseLog + tail)`. -/
theorem exponential_perturbation_majorant
    (baseLog tail : ℝ)
    (htail : 0 ≤ tail) :
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
      tail * Real.exp (baseLog + tail) := by
  have htail_exp := exp_sub_one_le_mul_exp tail htail
  have hbase_nonneg : 0 ≤ Real.exp baseLog := le_of_lt (Real.exp_pos baseLog)
  have hmul :
      Real.exp baseLog * (Real.exp tail - 1) ≤
        Real.exp baseLog * (tail * Real.exp tail) :=
    mul_le_mul_of_nonneg_left htail_exp hbase_nonneg
  calc
    Real.exp (baseLog + tail) - Real.exp baseLog =
        Real.exp baseLog * (Real.exp tail - 1) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp baseLog * (tail * Real.exp tail) := hmul
    _ = tail * Real.exp (baseLog + tail) := by
      rw [Real.exp_add]
      ring

/-- On a bounded logarithmic ball, replacing the tail by any larger
nonnegative envelope changes only the exponential prefactor. -/
theorem bounded_ball_exponential_tail
    (baseLog tail M envelope : ℝ)
    (hbaseLog : baseLog ≤ M)
    (htail0 : 0 ≤ tail)
    (henvelope0 : 0 ≤ envelope)
    (htail : tail ≤ envelope) :
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
      envelope * Real.exp (M + envelope) := by
  have hperturb := exponential_perturbation_majorant baseLog tail htail0
  have hsum : baseLog + tail ≤ M + envelope := add_le_add hbaseLog htail
  have hexp : Real.exp (baseLog + tail) ≤ Real.exp (M + envelope) :=
    Real.exp_le_exp.mpr hsum
  have htail_nonneg : 0 ≤ Real.exp (baseLog + tail) :=
    le_of_lt (Real.exp_pos (baseLog + tail))
  have hfirst :
      tail * Real.exp (baseLog + tail) ≤
        envelope * Real.exp (baseLog + tail) :=
    mul_le_mul_of_nonneg_right htail htail_nonneg
  have hsecond :
      envelope * Real.exp (baseLog + tail) ≤
        envelope * Real.exp (M + envelope) :=
    mul_le_mul_of_nonneg_left hexp henvelope0
  exact hperturb.trans (hfirst.trans hsecond)

/-- If a connected-log tail has an exponential/small decay envelope
`C * decay` with `decay <= 1`, scalar exponentiation preserves exactly the same
`decay` factor.  The only loss is the regulator-independent prefactor
`C * exp(M + C)` once `M` and `C` are uniform. -/
theorem exponential_tail_preserves_decay
    (baseLog tail M C decay : ℝ)
    (hbaseLog : baseLog ≤ M)
    (htail0 : 0 ≤ tail)
    (hC : 0 ≤ C)
    (hdecay0 : 0 ≤ decay)
    (hdecay1 : decay ≤ 1)
    (htail : tail ≤ C * decay) :
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
      (C * Real.exp (M + C)) * decay := by
  have henvelope0 : 0 ≤ C * decay := mul_nonneg hC hdecay0
  have hbound := bounded_ball_exponential_tail
    baseLog tail M (C * decay) hbaseLog htail0 henvelope0 htail
  have hCdecay : C * decay ≤ C := by
    nlinarith
  have hexp : Real.exp (M + C * decay) ≤ Real.exp (M + C) :=
    Real.exp_le_exp.mpr (add_le_add_left hCdecay M)
  have hleft_nonneg : 0 ≤ C * decay := mul_nonneg hC hdecay0
  have hmono :
      (C * decay) * Real.exp (M + C * decay) ≤
        (C * decay) * Real.exp (M + C) :=
    mul_le_mul_of_nonneg_left hexp hleft_nonneg
  calc
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
        (C * decay) * Real.exp (M + C * decay) := hbound
    _ ≤ (C * decay) * Real.exp (M + C) := hmono
    _ = (C * Real.exp (M + C)) * decay := by ring

#print axioms exp_sub_one_le_mul_exp
#print axioms exponential_perturbation_majorant
#print axioms bounded_ball_exponential_tail
#print axioms exponential_tail_preserves_decay

end Millennium.YangMills.FaizalShabirConnectedLogExponentialRecertification
