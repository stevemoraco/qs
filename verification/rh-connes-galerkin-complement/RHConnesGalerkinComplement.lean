import Mathlib

namespace RHConnesGalerkinComplement

/-- A bounded scalar cross term costs at most `beta` times the two-block norm. -/
theorem cross_term_floor
    (c beta x y : ℝ)
    (hbeta : 0 ≤ beta)
    (hc : |c| ≤ beta) :
    -beta * (x ^ 2 + y ^ 2) ≤ 2 * c * x * y := by
  rw [abs_le] at hc
  by_cases hxy : 0 ≤ x * y
  · have hcoef : (-beta) * (x * y) ≤ c * (x * y) :=
      mul_le_mul_of_nonneg_right hc.1 hxy
    have hgeom : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    have hgeom' : beta * (2 * x * y) ≤ beta * (x ^ 2 + y ^ 2) :=
      mul_le_mul_of_nonneg_left hgeom hbeta
    nlinarith
  · have hxy' : x * y ≤ 0 := le_of_not_ge hxy
    have hcoef : beta * (x * y) ≤ c * (x * y) :=
      mul_le_mul_of_nonpos_right hc.2 hxy'
    have hgeom : -(x ^ 2 + y ^ 2) ≤ 2 * x * y := by
      nlinarith [sq_nonneg (x + y)]
    have hgeom' : beta * (-(x ^ 2 + y ^ 2)) ≤ beta * (2 * x * y) :=
      mul_le_mul_of_nonneg_left hgeom hbeta
    nlinarith

/--
Finite quadratic-form core: diagonal block floors plus an absolute cross bound
produce a global floor lowered by exactly `beta`.
-/
theorem two_block_coercive
    (b d c b0 d0 beta x y : ℝ)
    (hbeta : 0 ≤ beta)
    (hb : b0 ≤ b)
    (hd : d0 ≤ d)
    (hc : |c| ≤ beta) :
    (min b0 d0 - beta) * (x ^ 2 + y ^ 2)
      ≤ b * x ^ 2 + 2 * c * x * y + d * y ^ 2 := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hminb : min b0 d0 ≤ b := le_trans (min_le_left _ _) hb
  have hmind : min b0 d0 ≤ d := le_trans (min_le_right _ _) hd
  have hbx : min b0 d0 * x ^ 2 ≤ b * x ^ 2 :=
    mul_le_mul_of_nonneg_right hminb hx
  have hdy : min b0 d0 * y ^ 2 ≤ d * y ^ 2 :=
    mul_le_mul_of_nonneg_right hmind hy
  have hcross := cross_term_floor c beta x y hbeta hc
  nlinarith

/-- Exact finite compression can miss a lower orthogonal complement state. -/
theorem exact_compression_can_hide_ground :
    min (10 : ℝ) 0 = 0 ∧ 0 < (10 : ℝ) ∧ (10 : ℝ) < 20 := by
  norm_num

/-- Positive diagonal floors do not survive an uncontrolled cross coupling. -/
theorem positive_diagonal_cross_can_be_negative :
    0 < (1 : ℝ) ∧ 0 < (10 : ℝ) ∧
      (1 : ℝ) * 1 ^ 2 + 2 * 6 * 1 * (-1) + 10 * (-1) ^ 2 = -1 := by
  norm_num

/-- The interval-separation hypothesis is exactly a positive certified gap. -/
theorem certified_gap_margin
    (b0 s beta : ℝ)
    (hsep : b0 + beta < s - beta) :
    0 < s - b0 - 2 * beta := by
  linarith

#print axioms RHConnesGalerkinComplement.cross_term_floor
#print axioms RHConnesGalerkinComplement.two_block_coercive
#print axioms RHConnesGalerkinComplement.exact_compression_can_hide_ground
#print axioms RHConnesGalerkinComplement.positive_diagonal_cross_can_be_negative
#print axioms RHConnesGalerkinComplement.certified_gap_margin

end RHConnesGalerkinComplement
