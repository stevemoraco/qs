import Mathlib

/-!
# Matched Mehler/engineering block-product capacity

Finite scalar synthesis of two independently banked Yang--Mills repair ledgers:

* the hypercontractive block-product debt; and
* the engineering-dimension-six linear contraction reserve.

Write `b2 = b^2` and `rho2 = rho^2`.  At the matched one-particle
boundary `rho2 * b2 = 1`, the denominator-cleared `r`-factor
hypercontractive debt is governed exactly by

`r * (p - 1) - b2 * (p - r)`.

Thus a finite exponent `p` is possible only below the sharp multiplicity
capacity `r < b2`; when `r < b2`, the explicit sufficient ticket is

`r * (b2 - 1) <= p * (b2 - r)`.

For the standard factor-two block, a stronger matched hypothesis
`rho * b <= 1` and engineering ticket `eta * b^2 <= 1` improve the
dimension-six ideal block from the previously banked `1/4` envelope to
`1/16`, leaving a `15/16` additive defect reserve.  The two-factor `L^6`
and three-factor `L^12` debts are then strictly negative, while every
exact-boundary multiplicity `r >= 4` is impossible for every finite `p > r`.

This file proves only finite real algebra.  It does not construct a matched
Gaussian covariance, prove a Mehler/second-quantized contraction, identify
the source's locality weight with a Gaussian correlation coefficient,
formalize Nelson--Gross hypercontractivity, engineering localization,
polymer norms, gauge fields, Yang--Mills, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.MatchedMehlerEngineeringCapacity

/-- Denominator-cleared hypercontractive block-product debt. -/
def blockProductDebt (r p rho2 : ℝ) : ℝ :=
  r * rho2 * (p - 1) - (p - r)

/-- Numerator controlling the debt at the matched boundary
`rho2 * b2 = 1`. -/
def matchedDebtNumerator (b2 r p : ℝ) : ℝ :=
  r * (p - 1) - b2 * (p - r)

/-- Exact boundary identity after multiplication by the positive scale
denominator. -/
theorem matchedDebt_scaled_identity
    (b2 r p rho2 : ℝ)
    (hmatch : rho2 * b2 = 1) :
    b2 * blockProductDebt r p rho2 =
      matchedDebtNumerator b2 r p := by
  unfold blockProductDebt matchedDebtNumerator
  calc
    b2 * (r * rho2 * (p - 1) - (p - r)) =
        r * (rho2 * b2) * (p - 1) - b2 * (p - r) := by ring
    _ = r * (p - 1) - b2 * (p - r) := by
      rw [hmatch]
      ring

/-- Useful factorization of the matched numerator. -/
theorem matchedDebtNumerator_factor
    (b2 r p : ℝ) :
    matchedDebtNumerator b2 r p =
      p * (r - b2) + r * (b2 - 1) := by
  unfold matchedDebtNumerator
  ring

/-- A submatched one-particle contraction plus a nonpositive matched
numerator pays the complete block-product debt. -/
theorem debt_nonpositive_of_submatched
    (b2 r p rho2 : ℝ)
    (hb2 : 0 < b2)
    (hr : 0 ≤ r)
    (hp : 1 ≤ p)
    (hrho : rho2 * b2 ≤ 1)
    (hnum : matchedDebtNumerator b2 r p ≤ 0) :
    blockProductDebt r p rho2 ≤ 0 := by
  have hfac : 0 ≤ r * (p - 1) :=
    mul_nonneg hr (sub_nonneg.mpr hp)
  have hmul1 :
      (r * (p - 1)) * (rho2 * b2) ≤
        (r * (p - 1)) * 1 :=
    mul_le_mul_of_nonneg_left hrho hfac
  have hnum' : r * (p - 1) ≤ b2 * (p - r) := by
    unfold matchedDebtNumerator at hnum
    linarith
  have hmul2 :
      (r * (p - 1)) * (rho2 * b2) ≤ b2 * (p - r) := by
    exact hmul1.trans (by simpa using hnum')
  have hscaled :
      b2 * (r * rho2 * (p - 1)) ≤ b2 * (p - r) := by
    calc
      b2 * (r * rho2 * (p - 1)) =
          (r * (p - 1)) * (rho2 * b2) := by ring
      _ ≤ b2 * (p - r) := hmul2
  have hcore : r * rho2 * (p - 1) ≤ p - r := by
    by_contra hnot
    have hrev : p - r < r * rho2 * (p - 1) := lt_of_not_ge hnot
    have hstrict :
        b2 * (p - r) < b2 * (r * rho2 * (p - 1)) :=
      mul_lt_mul_of_pos_left hrev hb2
    linarith
  unfold blockProductDebt
  linarith

/-- The explicit finite-exponent ticket below the matched multiplicity
capacity. -/
theorem matchedDebtNumerator_nonpositive_of_threshold
    (b2 r p : ℝ)
    (hthreshold : r * (b2 - 1) ≤ p * (b2 - r)) :
    matchedDebtNumerator b2 r p ≤ 0 := by
  rw [matchedDebtNumerator_factor]
  nlinarith

/-- Combined matched/submatched block-product ticket. -/
theorem matched_block_product_ticket
    (b2 r p rho2 : ℝ)
    (hb2 : 0 < b2)
    (hr : 0 ≤ r)
    (hp : 1 ≤ p)
    (hrho : rho2 * b2 ≤ 1)
    (hthreshold : r * (b2 - 1) ≤ p * (b2 - r)) :
    blockProductDebt r p rho2 ≤ 0 := by
  exact debt_nonpositive_of_submatched b2 r p rho2 hb2 hr hp hrho
    (matchedDebtNumerator_nonpositive_of_threshold b2 r p hthreshold)

/-- At or above the scale-squared multiplicity, the matched numerator is
strictly positive for every finite exponent `p > r`. -/
theorem matchedDebtNumerator_positive_of_capacity_failure
    (b2 r p : ℝ)
    (hb2 : 1 < b2)
    (hbr : b2 ≤ r)
    (hrp : r < p) :
    0 < matchedDebtNumerator b2 r p := by
  rw [matchedDebtNumerator_factor]
  have hr0 : 0 < r := by linarith
  have hp0 : 0 < p := lt_trans hr0 hrp
  have hfirst : 0 ≤ p * (r - b2) :=
    mul_nonneg (le_of_lt hp0) (sub_nonneg.mpr hbr)
  have hsecond : 0 < r * (b2 - 1) :=
    mul_pos hr0 (sub_pos.mpr hb2)
  linarith

/-- Sharp matched-boundary obstruction: `r >= b2` makes every finite
`p > r` debt strictly positive. -/
theorem boundary_debt_positive_of_capacity_failure
    (b2 r p rho2 : ℝ)
    (hb2 : 1 < b2)
    (hbr : b2 ≤ r)
    (hrp : r < p)
    (hmatch : rho2 * b2 = 1) :
    0 < blockProductDebt r p rho2 := by
  have hb20 : 0 < b2 := by linarith
  have hnum :
      0 < matchedDebtNumerator b2 r p :=
    matchedDebtNumerator_positive_of_capacity_failure b2 r p hb2 hbr hrp
  have hscaled :
      0 < b2 * blockProductDebt r p rho2 := by
    rw [matchedDebt_scaled_identity b2 r p rho2 hmatch]
    exact hnum
  by_contra hnot
  have hdebt : blockProductDebt r p rho2 ≤ 0 := le_of_not_gt hnot
  have hprod : b2 * blockProductDebt r p rho2 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb20) hdebt
  linarith

/-- Concrete factor-two/two-factor shell.  A matched or stronger
`rho^2 ≤ 1/4` gives strictly negative `L^6` debt. -/
theorem factorTwo_twoFactorL6_strict
    (rho2 : ℝ)
    (hrho : 4 * rho2 ≤ 1) :
    blockProductDebt 2 6 rho2 < 0 := by
  unfold blockProductDebt
  nlinarith

/-- Concrete factor-two/three-factor shell.  A matched or stronger
`rho^2 ≤ 1/4` gives strictly negative `L^12` debt. -/
theorem factorTwo_threeFactorL12_strict
    (rho2 : ℝ)
    (hrho : 4 * rho2 ≤ 1) :
    blockProductDebt 3 12 rho2 < 0 := by
  unfold blockProductDebt
  nlinarith

/-- At exact factor-two matching, every multiplicity `r ≥ 4` lies beyond
the finite-exponent capacity. -/
theorem factorTwo_fourOrMore_boundary_impossible
    (r p rho2 : ℝ)
    (hr : 4 ≤ r)
    (hp : r < p)
    (hmatch : rho2 * 4 = 1) :
    0 < blockProductDebt r p rho2 := by
  exact boundary_debt_positive_of_capacity_failure
    4 r p rho2 (by norm_num) hr hp hmatch

/-- Joint multiplier for a derivative-quadratic dimension-six mode. -/
def derivativeQuadraticMultiplier (rho eta : ℝ) : ℝ :=
  rho ^ 2 * eta

/-- Joint multiplier for a cubic dimension-six mode. -/
def cubicMultiplier (rho eta : ℝ) : ℝ :=
  rho ^ 3 * eta

/-- A matched one-particle contraction and matched engineering scaling give
the exact denominator-free `b^4` quadratic envelope. -/
theorem matched_quadratic_scaled_bound
    (b rho eta : ℝ)
    (hb0 : 0 ≤ b)
    (hrho0 : 0 ≤ rho)
    (hrho : rho * b ≤ 1)
    (heta0 : 0 ≤ eta)
    (heta : eta * b ^ 2 ≤ 1) :
    derivativeQuadraticMultiplier rho eta * b ^ 4 ≤ 1 := by
  have hx0 : 0 ≤ rho * b := mul_nonneg hrho0 hb0
  have hxgap : 0 ≤ (rho * b) * (1 - rho * b) :=
    mul_nonneg hx0 (sub_nonneg.mpr hrho)
  have hx2 : (rho * b) ^ 2 ≤ 1 := by
    nlinarith
  have hy0 : 0 ≤ eta * b ^ 2 :=
    mul_nonneg heta0 (sq_nonneg b)
  have hprod1 :
      (rho * b) ^ 2 * (eta * b ^ 2) ≤
        1 * (eta * b ^ 2) :=
    mul_le_mul_of_nonneg_right hx2 hy0
  have hprod2 :
      1 * (eta * b ^ 2) ≤ 1 * 1 :=
    mul_le_mul_of_nonneg_left heta (by norm_num)
  calc
    derivativeQuadraticMultiplier rho eta * b ^ 4 =
        (rho * b) ^ 2 * (eta * b ^ 2) := by
      unfold derivativeQuadraticMultiplier
      ring
    _ ≤ 1 * (eta * b ^ 2) := hprod1
    _ ≤ 1 * 1 := hprod2
    _ = 1 := by ring

/-- Under a genuine block factor `b ≥ 2`, the matched conditions imply
`rho ≤ 1/2`. -/
theorem rho_le_half_of_matched_block
    (b rho : ℝ)
    (hb : 2 ≤ b)
    (hrho0 : 0 ≤ rho)
    (hrho : rho * b ≤ 1) :
    rho ≤ (1 / 2 : ℝ) := by
  have hscale : rho * 2 ≤ rho * b :=
    mul_le_mul_of_nonneg_left hb hrho0
  nlinarith

/-- Under `b ≥ 2`, a matched engineering ticket implies `eta ≤ 1/4`. -/
theorem eta_le_quarter_of_matched_engineering
    (b eta : ℝ)
    (hb : 2 ≤ b)
    (heta0 : 0 ≤ eta)
    (heta : eta * b ^ 2 ≤ 1) :
    eta ≤ (1 / 4 : ℝ) := by
  have hbplus : 0 ≤ b + 2 := by linarith
  have hprod : 0 ≤ (b - 2) * (b + 2) :=
    mul_nonneg (sub_nonneg.mpr hb) hbplus
  have hb2 : 4 ≤ b ^ 2 := by
    nlinarith
  have hscale : eta * 4 ≤ eta * b ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 heta0
  nlinarith

/-- On the interval `rho ≤ 1`, the cubic multiplier is no larger than the
quadratic multiplier. -/
theorem cubic_le_quadratic
    (rho eta : ℝ)
    (hrho1 : rho ≤ 1)
    (heta0 : 0 ≤ eta) :
    cubicMultiplier rho eta ≤
      derivativeQuadraticMultiplier rho eta := by
  have hgap : 0 ≤ rho ^ 2 * (1 - rho) :=
    mul_nonneg (sq_nonneg rho) (sub_nonneg.mpr hrho1)
  have hc2 : rho ^ 3 ≤ rho ^ 2 := by
    nlinarith
  unfold cubicMultiplier derivativeQuadraticMultiplier
  exact mul_le_mul_of_nonneg_right hc2 heta0

/-- Matched factor-two-or-larger scaling improves the ideal dimension-six
block envelope from `1/4` to `1/16`. -/
theorem matched_dimension_six_block_le_sixteenth
    (b rho eta : ℝ)
    (hb : 2 ≤ b)
    (hrho0 : 0 ≤ rho)
    (hrho : rho * b ≤ 1)
    (heta0 : 0 ≤ eta)
    (heta : eta * b ^ 2 ≤ 1) :
    max (derivativeQuadraticMultiplier rho eta)
        (cubicMultiplier rho eta) ≤ (1 / 16 : ℝ) := by
  have hrhohalf :
      rho ≤ (1 / 2 : ℝ) :=
    rho_le_half_of_matched_block b rho hb hrho0 hrho
  have hrhogap : 0 ≤ rho * ((1 / 2 : ℝ) - rho) :=
    mul_nonneg hrho0 (sub_nonneg.mpr hrhohalf)
  have hrho2 : rho ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith
  have hetaquarter :
      eta ≤ (1 / 4 : ℝ) :=
    eta_le_quarter_of_matched_engineering b eta hb heta0 heta
  have hquad :
      derivativeQuadraticMultiplier rho eta ≤ (1 / 16 : ℝ) := by
    have hmul :
        rho ^ 2 * eta ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) :=
      mul_le_mul hrho2 hetaquarter heta0 (by norm_num)
    unfold derivativeQuadraticMultiplier
    calc
      rho ^ 2 * eta ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) := hmul
      _ = (1 / 16 : ℝ) := by norm_num
  have hrho1 : rho ≤ 1 := by linarith
  have hcubic :
      cubicMultiplier rho eta ≤ (1 / 16 : ℝ) :=
    (cubic_le_quadratic rho eta hrho1 heta0).trans hquad
  exact max_le hquad hcubic

/-- A sixteenth ideal block leaves a fifteen-sixteenths additive defect
budget before loss of nonexpansivity. -/
theorem sixteenth_plus_defect_le_one
    (ideal defect : ℝ)
    (hideal : ideal ≤ (1 / 16 : ℝ))
    (hdefect : defect ≤ (15 / 16 : ℝ)) :
    ideal + defect ≤ 1 := by
  linarith

/-- Strict use of the `15/16` reserve gives one-step contraction. -/
theorem strict_contraction_inside_fifteen_sixteenth_reserve
    (x xnext ideal defect : ℝ)
    (hx : 0 < x)
    (hideal : ideal ≤ (1 / 16 : ℝ))
    (hdefect : defect < (15 / 16 : ℝ))
    (hstep : xnext ≤ (ideal + defect) * x) :
    xnext < x := by
  have hcoef : ideal + defect < 1 := by linarith
  have hmul : (ideal + defect) * x < 1 * x :=
    mul_lt_mul_of_pos_right hcoef hx
  exact lt_of_le_of_lt hstep (by simpa using hmul)

/-- Integrated factor-two finite scalar bundle: both block-product shells are
strictly admissible and the dimension-six ideal block is at most `1/16`. -/
theorem factorTwo_matched_bundle
    (rho eta : ℝ)
    (hrho0 : 0 ≤ rho)
    (hrho : rho * 2 ≤ 1)
    (heta0 : 0 ≤ eta)
    (heta : eta * 4 ≤ 1) :
    blockProductDebt 2 6 (rho ^ 2) < 0 ∧
    blockProductDebt 3 12 (rho ^ 2) < 0 ∧
    max (derivativeQuadraticMultiplier rho eta)
        (cubicMultiplier rho eta) ≤ (1 / 16 : ℝ) := by
  have hrhohalf : rho ≤ (1 / 2 : ℝ) := by
    nlinarith
  have hgap : 0 ≤ rho * ((1 / 2 : ℝ) - rho) :=
    mul_nonneg hrho0 (sub_nonneg.mpr hrhohalf)
  have hrho2 : 4 * rho ^ 2 ≤ 1 := by
    nlinarith
  have heta' : eta * (2 : ℝ) ^ 2 ≤ 1 := by
    norm_num at heta ⊢
    exact heta
  constructor
  · exact factorTwo_twoFactorL6_strict (rho ^ 2) hrho2
  constructor
  · exact factorTwo_threeFactorL12_strict (rho ^ 2) hrho2
  · exact matched_dimension_six_block_le_sixteenth
      2 rho eta (by norm_num) hrho0 hrho heta0 heta'

#print axioms matchedDebt_scaled_identity
#print axioms matchedDebtNumerator_factor
#print axioms debt_nonpositive_of_submatched
#print axioms matchedDebtNumerator_nonpositive_of_threshold
#print axioms matched_block_product_ticket
#print axioms matchedDebtNumerator_positive_of_capacity_failure
#print axioms boundary_debt_positive_of_capacity_failure
#print axioms factorTwo_twoFactorL6_strict
#print axioms factorTwo_threeFactorL12_strict
#print axioms factorTwo_fourOrMore_boundary_impossible
#print axioms matched_quadratic_scaled_bound
#print axioms rho_le_half_of_matched_block
#print axioms eta_le_quarter_of_matched_engineering
#print axioms cubic_le_quadratic
#print axioms matched_dimension_six_block_le_sixteenth
#print axioms sixteenth_plus_defect_le_one
#print axioms strict_contraction_inside_fifteen_sixteenth_reserve
#print axioms factorTwo_matched_bundle

end Millennium.YangMills.MatchedMehlerEngineeringCapacity
