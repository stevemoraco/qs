import Mathlib

/-!
# Faizal--Shabir connected-log exponential recertification

Finite real-exponential and finite Schur row/column majorants for the
model-facing repair gate `YM-FS-CONNECTED-LOG-TAIL-TO-OS-SCHUR`.

The analytic operator theorem still has to place the connected logarithm and
its collar tail in one regulator/volume/scale-uniform submultiplicative Schur
(or stronger Banach-algebra) norm. Once that is supplied, the standard
noncommutative exponential perturbation estimate shows that exponentiation
changes only a bounded prefactor, not the tail exponent.

This file kernelizes only finite/scalar majorants. It does not formalize
polymer activities, infinite kernels, operator exponentials,
Osterwalder--Schrader transfer operators, Yang--Mills, a mass gap, or a Clay
theorem.
-/

namespace Millennium.YangMills.FaizalShabirConnectedLogExponentialRecertification

open scoped BigOperators

/-- Elementary exponential remainder bound used as the scalar majorant for the
Banach-algebra exponential perturbation estimate. -/
theorem exp_sub_one_le_mul_exp (x : ℝ) :
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

/-- An additive logarithmic tail changes the scalar exponential by at most
`tail * exp(baseLog + tail)` in scalar order. -/
theorem exponential_perturbation_majorant
    (baseLog tail : ℝ) :
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
      tail * Real.exp (baseLog + tail) := by
  have htail_exp := exp_sub_one_le_mul_exp tail
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
    (henvelope0 : 0 ≤ envelope)
    (htail : tail ≤ envelope) :
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
      envelope * Real.exp (M + envelope) := by
  have hperturb := exponential_perturbation_majorant baseLog tail
  have hsum : baseLog + tail ≤ M + envelope := add_le_add hbaseLog htail
  have hexp : Real.exp (baseLog + tail) ≤ Real.exp (M + envelope) :=
    Real.exp_le_exp.mpr hsum
  have hexp_nonneg : 0 ≤ Real.exp (baseLog + tail) :=
    le_of_lt (Real.exp_pos (baseLog + tail))
  have hfirst :
      tail * Real.exp (baseLog + tail) ≤
        envelope * Real.exp (baseLog + tail) :=
    mul_le_mul_of_nonneg_right htail hexp_nonneg
  have hsecond :
      envelope * Real.exp (baseLog + tail) ≤
        envelope * Real.exp (M + envelope) :=
    mul_le_mul_of_nonneg_left hexp henvelope0
  exact hperturb.trans (hfirst.trans hsecond)

/-- If a connected-log tail has an exponential/small decay envelope
`C * decay` with `decay <= 1`, scalar exponentiation preserves exactly the same
`decay` factor. The only loss is the regulator-independent prefactor
`C * exp(M + C)` once `M` and `C` are uniform. -/
theorem exponential_tail_preserves_decay
    (baseLog tail M C decay : ℝ)
    (hbaseLog : baseLog ≤ M)
    (hC : 0 ≤ C)
    (hdecay0 : 0 ≤ decay)
    (hdecay1 : decay ≤ 1)
    (htail : tail ≤ C * decay) :
    Real.exp (baseLog + tail) - Real.exp baseLog ≤
      (C * Real.exp (M + C)) * decay := by
  have henvelope0 : 0 ≤ C * decay := mul_nonneg hC hdecay0
  have hbound := bounded_ball_exponential_tail
    baseLog tail M (C * decay) hbaseLog henvelope0 htail
  have hCdecay : C * decay ≤ C := by
    nlinarith
  have hsumC : M + C * decay ≤ M + C := by
    linarith
  have hexp : Real.exp (M + C * decay) ≤ Real.exp (M + C) :=
    Real.exp_le_exp.mpr hsumC
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

/-- Finite nonnegative kernel row bounds are submultiplicative under kernel
composition. This is the finite Schur-row algebra consumed by the abstract
exponential recertification once actual absolute kernel coefficients are
supplied. -/
theorem nonnegative_kernel_row_composition
    {ι : Type*} [Fintype ι]
    (K L : ι → ι → ℝ)
    (rK rL : ℝ)
    (hKnonneg : ∀ i j, 0 ≤ K i j)
    (hKrow : ∀ i, (∑ j, K i j) ≤ rK)
    (hLrow : ∀ j, (∑ k, L j k) ≤ rL)
    (hrL : 0 ≤ rL) :
    ∀ i, (∑ k, ∑ j, K i j * L j k) ≤ rK * rL := by
  intro i
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ k, K i j * L j k) =
        ∑ j, K i j * (∑ k, L j k) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    _ ≤ ∑ j, K i j * rL := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hLrow j) (hKnonneg i j)
    _ = (∑ j, K i j) * rL := by
      rw [Finset.sum_mul]
    _ ≤ rK * rL := mul_le_mul_of_nonneg_right (hKrow i) hrL

/-- Finite nonnegative kernel column bounds are likewise submultiplicative. -/
theorem nonnegative_kernel_column_composition
    {ι : Type*} [Fintype ι]
    (K L : ι → ι → ℝ)
    (cK cL : ℝ)
    (hLnonneg : ∀ j k, 0 ≤ L j k)
    (hKcol : ∀ j, (∑ i, K i j) ≤ cK)
    (hLcol : ∀ k, (∑ j, L j k) ≤ cL)
    (hcK : 0 ≤ cK) :
    ∀ k, (∑ i, ∑ j, K i j * L j k) ≤ cK * cL := by
  intro k
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, K i j * L j k) =
        ∑ j, (∑ i, K i j) * L j k := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ ≤ ∑ j, cK * L j k := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (hKcol j) (hLnonneg j k)
    _ = cK * (∑ j, L j k) := by
      rw [Finset.mul_sum]
    _ ≤ cK * cL := mul_le_mul_of_nonneg_left (hLcol k) hcK

#print axioms exp_sub_one_le_mul_exp
#print axioms exponential_perturbation_majorant
#print axioms bounded_ball_exponential_tail
#print axioms exponential_tail_preserves_decay
#print axioms nonnegative_kernel_row_composition
#print axioms nonnegative_kernel_column_composition

end Millennium.YangMills.FaizalShabirConnectedLogExponentialRecertification
