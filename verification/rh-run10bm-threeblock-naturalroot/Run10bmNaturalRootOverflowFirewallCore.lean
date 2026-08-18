import Mathlib

namespace Millennium.RH

/-- Exact square excess of the literal `101/100` cap over one. -/
theorem run10bma_cap_square_excess :
    (101 / 100 : ℝ) ^ 2 - 1 = 201 / 10000 := by
  norm_num

/-- Scalar determinant consumer for the one-`AB` quadratic-root architecture.

The analytic/finite-dimensional producer is the implication
`sigma_max(B)>101/100 -> det((101/100)^2 I - B B^T)<0`, with
`B B^T = [[1, 2*alpha*rB], [2*alpha*rB, beta^2]]`.
This theorem deliberately formalizes only the resulting real inequality. -/
theorem run10bma_crossing_forces_first_split
    (alpha beta rB : ℝ)
    (ha : 0 ≤ alpha)
    (hbeta : beta ^ 2 ≤ 1)
    (hrB : rB ^ 2 ≤ 1)
    (hdet :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) <
        4 * alpha ^ 2 * rB ^ 2) :
    (201 / 20000 : ℝ) < alpha := by
  rw [run10bma_cap_square_excess] at hdet
  have hq : (101 / 100 : ℝ) ^ 2 = 10201 / 10000 := by
    norm_num
  have hcapbeta :
      (201 / 10000 : ℝ) ≤ (101 / 100 : ℝ) ^ 2 - beta ^ 2 := by
    rw [hq]
    nlinarith [hbeta]
  have hcpos : (0 : ℝ) ≤ 201 / 10000 := by
    norm_num
  have hlower :
      (201 / 10000 : ℝ) ^ 2 ≤
        (201 / 10000 : ℝ) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hcapbeta hcpos
  have ha2 : 0 ≤ 4 * alpha ^ 2 := by
    positivity
  have hupper : 4 * alpha ^ 2 * rB ^ 2 ≤ 4 * alpha ^ 2 := by
    calc
      4 * alpha ^ 2 * rB ^ 2 ≤ 4 * alpha ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hrB ha2
      _ = 4 * alpha ^ 2 := by ring
  have hsquare :
      (201 / 10000 : ℝ) ^ 2 < 4 * alpha ^ 2 := by
    linarith
  nlinarith

/-- Once the cap-crossing producer gives the first-split lower bound, the
signed `ABC^2` resonance support exponent `1+alpha` is already strictly above
`20201/20000 = 1.01005`. -/
theorem run10bma_signed_support_overflow
    (alpha : ℝ)
    (ha : (201 / 20000 : ℝ) < alpha) :
    (20201 / 20000 : ℝ) < 1 + alpha := by
  linarith

/-- If the high-block odd coefficient is removed, the active two-block ideal
norm stays below one whenever the `AB` root is genuinely natural and the
second RMS is strictly below its exponent endpoint. -/
theorem run10bma_no_high_block_no_crossing
    (alpha beta rB : ℝ)
    (hrB : rB < beta)
    (hnatural : alpha + beta ≤ 1) :
    alpha + rB < (101 / 100 : ℝ) := by
  linarith

/-- A nonzero quadratic `AB` coefficient and nonzero high-block linear
coefficient force the algebraic `ABC^2` coefficient `-2*t*z` to be nonzero. -/
theorem run10bma_abc2_coefficient_nonzero
    (t z : ℝ)
    (ht : t ≠ 0)
    (hz : z ≠ 0) :
    -(2 : ℝ) * t * z ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) ht) hz

#check run10bma_cap_square_excess
#print axioms run10bma_cap_square_excess
#check run10bma_crossing_forces_first_split
#print axioms run10bma_crossing_forces_first_split
#check run10bma_signed_support_overflow
#print axioms run10bma_signed_support_overflow
#check run10bma_no_high_block_no_crossing
#print axioms run10bma_no_high_block_no_crossing
#check run10bma_abc2_coefficient_nonzero
#print axioms run10bma_abc2_coefficient_nonzero

end Millennium.RH
