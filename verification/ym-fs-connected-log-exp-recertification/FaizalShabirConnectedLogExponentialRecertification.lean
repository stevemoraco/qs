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
  at most `tail * exp(local + tail)`;
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
        rw [Real.exp_add]
      _ = 1 := by simp
  calc
    Real.exp x - 1 = (1 - Real.exp (-x)) * Real.exp x := by
      rw [sub_mul, one_mul, hinv]
    _ ≤ x * Real.exp x := hmul

/-- A nonnegative additive logarithmic tail changes the scalar exponential by
at most `tail * exp(local + tail)`. -/
theorem exponential_perturbation_majorant
    (local tail : ℝ)
    (htail : 0 ≤ tail) :
    Real.exp (local + tail) - Real.exp local ≤
      tail * Real.exp (local + tail) := by
  have htail_exp := exp_sub_one_le_mul_exp tail htail
  have hlocal_nonneg : 0 ≤ Real.exp local := le_of_lt (Real.exp_pos local)
  have hmul :
      Real.exp local * (Real.exp tail - 1) ≤
        Real.exp local * (tail * Real.exp tail) :=
    mul_le_mul_of_nonneg_left htail_exp hlocal_nonneg
  calc
    Real.exp (local + tail) - Real.exp local =
        Real.exp local * (Real.exp tail - 1) := by
      rw [Real.exp_add]
      ring
    _ ≤ Real.exp local * (tail * Real.exp tail) := hmul
    _ = tail * Real.exp (local + tail) := by
      rw [Real.exp_add]
      ring

/-- On a bounded logarithmic ball, replacing the tail by any larger
nonnegative envelope changes only the exponential prefactor. -/
theorem bounded_ball_exponential_tail
    (local tail M envelope : ℝ)
    (hlocal : local ≤ M)
    (htail0 : 0 ≤ tail)
    (henvelope0 : 0 ≤ envelope)
    (htail : tail ≤ envelope) :
    Real.exp (local + tail) - Real.exp local ≤
      envelope * Real.exp (M + envelope) := by
  have hperturb := exponential_perturbation_majorant local tail htail0
  have hsum : local + tail ≤ M + envelope := add_le_add hlocal htail
  have hexp : Real.exp (local + tail) ≤ Real.exp (M + envelope) :=
    Real.exp_le_exp.mpr hsum
  have htail_nonneg : 0 ≤ Real.exp (local + tail) :=
    le_of_lt (Real.exp_pos (local + tail))
  have hfirst :
      tail * Real.exp (local + tail) ≤
        envelope * Real.exp (local + tail) :=
    mul_le_mul_of_nonneg_right htail htail_nonneg
  have hsecond :
      envelope * Real.exp (local + tail) ≤
        envelope * Real.exp (M + envelope) :=
    mul_le_mul_of_nonneg_left hexp henvelope0
  exact hperturb.trans (hfirst.trans hsecond)

/-- If a connected-log tail has an exponential/small decay envelope
`C * decay` with `decay <= 1`, scalar exponentiation preserves exactly the same
`decay` factor.  The only loss is the regulator-independent prefactor
`C * exp(M + C)` once `M` and `C` are uniform. -/
theorem exponential_tail_preserves_decay
    (local tail M C decay : ℝ)
    (hlocal : local ≤ M)
    (htail0 : 0 ≤ tail)
    (hC : 0 ≤ C)
    (hdecay0 : 0 ≤ decay)
    (hdecay1 : decay ≤ 1)
    (htail : tail ≤ C * decay) :
    Real.exp (local + tail) - Real.exp local ≤
      (C * Real.exp (M + C)) * decay := by
  have henvelope0 : 0 ≤ C * decay := mul_nonneg hC hdecay0
  have hbase := bounded_ball_exponential_tail
    local tail M (C * decay) hlocal htail0 henvelope0 htail
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
    Real.exp (local + tail) - Real.exp local ≤
        (C * decay) * Real.exp (M + C * decay) := hbase
    _ ≤ (C * decay) * Real.exp (M + C) := hmono
    _ = (C * Real.exp (M + C)) * decay := by ring

#print axioms exp_sub_one_le_mul_exp
#print axioms exponential_perturbation_majorant
#print axioms bounded_ball_exponential_tail
#print axioms exponential_tail_preserves_decay

end Millennium.YangMills.FaizalShabirConnectedLogExponentialRecertification
