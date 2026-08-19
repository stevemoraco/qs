import Mathlib

namespace Millennium.RH

/-- Exact Pythagorean split used by Run10bs. This is finite rational
arithmetic only; the interpretation as prime-block variances is external. -/
theorem run10bs_pythagorean_split :
    (276 / 19045 : ℝ)^2 + (19043 / 19045 : ℝ)^2 = 1 := by
  norm_num

/-- Exact rational approximation to the optimal one-sided analytic tilt
coefficient `1/sqrt(2)`. -/
theorem run10bs_low_analytic_tilt_coefficient :
    (2 * (29 / 41 : ℝ)) /
        (1 + 2 * (29 / 41 : ℝ)^2) =
      (2378 / 3363 : ℝ) := by
  norm_num

/-- The exact rational hybrid tilt clears the raised prime-only cap. -/
theorem run10bs_hybrid_tilt_reserve :
    (19043 / 19045 : ℝ) +
        (2378 / 3363 : ℝ) * (276 / 19045 : ℝ) -
        (20201 / 20000 : ℝ) =
      (7888311 / 85397780000 : ℝ) := by
  norm_num

/-- The reserve above the raised cap is strictly positive. -/
theorem run10bs_hybrid_tilt_strict :
    (20201 / 20000 : ℝ) <
      (19043 / 19045 : ℝ) +
        (2378 / 3363 : ℝ) * (276 / 19045 : ℝ) := by
  norm_num

/-- The raised prime-only cap leaves the exact fixed margin `1/20000`
above the literal `1.01` threshold. -/
theorem run10bs_prime_power_margin :
    (20201 / 20000 : ℝ) - (101 / 100 : ℝ) = (1 / 20000 : ℝ) := by
  norm_num

/-- Exact common multiplicative support exponent of every hard Run10bs row. -/
theorem run10bs_hard_support :
    1 + (276 / 19045 : ℝ) = (19321 / 19045 : ℝ) := by
  norm_num

/-- Exact relative additive-shift exponent attached to the hard support. -/
theorem run10bs_hard_shift_exponent :
    (((19321 / 19045 : ℝ) - 1) /
        (19321 / 19045 : ℝ)) =
      (276 / 19321 : ℝ) := by
  norm_num

/-- The hard relative shift exponent is below `1/69`. -/
theorem run10bs_hard_shift_below_one_over_sixtynine :
    (276 / 19321 : ℝ) < (1 / 69 : ℝ) := by
  norm_num

/-- Finite support algebra for the first conjugate hard pair:
`min(2 alpha + 1, alpha + 1)=alpha+1` for nonnegative alpha. -/
theorem run10bs_hard_pair_low_cubic_support
    (alpha : ℝ) (ha : 0 ≤ alpha) :
    min (2 * alpha + 1) (alpha + 1) = alpha + 1 := by
  rw [min_eq_right]
  linarith

/-- Finite support algebra for the high-cubic hard pair:
`min(alpha+2,alpha+1)=alpha+1`. -/
theorem run10bs_hard_pair_high_cubic_support
    (alpha : ℝ) :
    min (alpha + 2) (alpha + 1) = alpha + 1 := by
  rw [min_eq_right]
  linarith

/-- Finite support algebra for the cross hard pair. The premise `alpha<=1`
is the only ingredient needed to identify `min(alpha+1,2)`. -/
theorem run10bs_hard_pair_cross_support
    (alpha : ℝ) (ha : alpha ≤ 1) :
    min (alpha + 1) 2 = alpha + 1 := by
  rw [min_eq_left]
  linarith

/-- The Cauchy last step behind the factorized multi-low-block firewall:
`u(2S-u) <= S^2`. The full RMS sum interpretation remains in the research
note; this theorem encodes only the scalar identity and inequality. -/
theorem run10bs_lowblock_cost_last_step
    (S u : ℝ) :
    u * (2 * S - u) ≤ S^2 := by
  nlinarith [sq_nonneg (S - u)]

/-- The central beyond-natural cap coefficient is strictly negative for the
literal Run10bs rational parameters. This is only scalar sign arithmetic;
it does not formalize the Fourier expansion that produces the coefficient. -/
theorem run10bs_central_hard_coefficient_negative :
    let alpha : ℝ := 276 / 19045
    let x : ℝ := 29 / 41
    let kappa : ℝ := x / alpha
    let s : ℝ := 19043 / 19045
    let q : ℝ := 20201 / 20000
    (kappa / 2) * (kappa * q - 2 * kappa * s - 1) < 0 := by
  norm_num

#check run10bs_pythagorean_split
#check run10bs_low_analytic_tilt_coefficient
#check run10bs_hybrid_tilt_reserve
#check run10bs_hybrid_tilt_strict
#check run10bs_prime_power_margin
#check run10bs_hard_support
#check run10bs_hard_shift_exponent
#check run10bs_hard_shift_below_one_over_sixtynine
#check run10bs_hard_pair_low_cubic_support
#check run10bs_hard_pair_high_cubic_support
#check run10bs_hard_pair_cross_support
#check run10bs_lowblock_cost_last_step
#check run10bs_central_hard_coefficient_negative

#print axioms run10bs_pythagorean_split
#print axioms run10bs_low_analytic_tilt_coefficient
#print axioms run10bs_hybrid_tilt_reserve
#print axioms run10bs_hybrid_tilt_strict
#print axioms run10bs_prime_power_margin
#print axioms run10bs_hard_support
#print axioms run10bs_hard_shift_exponent
#print axioms run10bs_hard_shift_below_one_over_sixtynine
#print axioms run10bs_hard_pair_low_cubic_support
#print axioms run10bs_hard_pair_high_cubic_support
#print axioms run10bs_hard_pair_cross_support
#print axioms run10bs_lowblock_cost_last_step
#print axioms run10bs_central_hard_coefficient_negative

end Millennium.RH
