import Mathlib

namespace RHDyadicThetaDepthSpine

/-- The Cauchy--Schwarz dyadic block exponent simplifies to the negative
of the available holomorphy margin. -/
theorem block_exponent_identity (alpha eps sigma : ℝ) :
    (1 + alpha / 2 + eps / 2) + (-sigma - 1 / 2) =
      -(sigma - 1 / 2 - alpha / 2 - eps / 2) := by
  ring

/-- If `alpha + eps < 2 * sigma - 1`, then the dyadic block exponent is
strictly decaying. -/
theorem positive_block_decay_margin
    (alpha eps sigma : ℝ)
    (hmargin : alpha + eps < 2 * sigma - 1) :
    0 < sigma - 1 / 2 - alpha / 2 - eps / 2 := by
  linarith

/-- The weighted-energy integrand exponent is exactly the critical `-1`
minus twice the remaining depth margin. -/
theorem weighted_energy_exponent_identity
    (theta eps delta : ℝ) :
    (1 + 2 * theta + 2 * eps) + (-2 - 2 * delta) =
      -1 - 2 * (delta - theta - eps) := by
  ring

/-- A positive weighted-energy margin places the power exponent strictly
below the integrability threshold `-1`. -/
theorem weighted_energy_exponent_lt_neg_one
    (theta eps delta : ℝ)
    (hmargin : theta + eps < delta) :
    (1 + 2 * theta + 2 * eps) + (-2 - 2 * delta) < -1 := by
  linarith

/-- The upper estimate `alpha ≤ 2*theta` and the Mellin obstruction
`theta ≤ alpha/2` force the exact depth law `alpha = 2*theta`. -/
theorem depth_sandwich
    (alpha theta : ℝ)
    (hupper : alpha ≤ 2 * theta)
    (hlower : theta ≤ alpha / 2) :
    alpha = 2 * theta := by
  linarith

/-- An abstract pole multiplier `(1-z)/rho` cannot vanish when both factors
are nonzero. This is the finite field-theoretic core used after proving
`rho ≠ 0` and `2^{-rho} ≠ 1`. -/
theorem pole_multiplier_nonzero
    {K : Type*} [Field K]
    (rho z : K)
    (hrho : rho ≠ 0)
    (hz : z ≠ 1) :
    (1 - z) / rho ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hz)) hrho

/-- A point strictly inside the unit disk is not the multiplicative unit. -/
theorem strict_norm_lt_one_ne_one
    (z : ℂ)
    (hz : ‖z‖ < 1) :
    z ≠ 1 := by
  intro h
  subst z
  norm_num at hz

#print axioms RHDyadicThetaDepthSpine.block_exponent_identity
#print axioms RHDyadicThetaDepthSpine.positive_block_decay_margin
#print axioms RHDyadicThetaDepthSpine.weighted_energy_exponent_identity
#print axioms RHDyadicThetaDepthSpine.weighted_energy_exponent_lt_neg_one
#print axioms RHDyadicThetaDepthSpine.depth_sandwich
#print axioms RHDyadicThetaDepthSpine.pole_multiplier_nonzero
#print axioms RHDyadicThetaDepthSpine.strict_norm_lt_one_ne_one

end RHDyadicThetaDepthSpine
