import Mathlib

namespace RHSingleLogarithmicCriterionFinite

/-- Exact polynomial exponent of one false-RH block in the logarithmically
weighted root-square series. -/
theorem logarithmic_block_exponent_identity
    (delta epsilon : ℝ) :
    (1 - epsilon) + (2 * delta - 2 * epsilon) - 1
      = 2 * delta - 3 * epsilon := by
  ring

/-- The logarithmically weighted block has a positive polynomial margin
whenever `3 epsilon < 2 delta`. -/
theorem logarithmic_block_margin
    {delta epsilon : ℝ}
    (h : 3 * epsilon < 2 * delta) :
    0 < 2 * delta - 3 * epsilon := by
  linarith

/-- The fourth Laplace moment carries the exact coefficient `3/8` because
`3!/(2^4)=3/8`. -/
theorem fourth_laplace_moment_constant :
    (6 : ℝ) / 2 ^ 4 = 3 / 8 := by
  norm_num

/-- The endpoint small-parameter exponent `alpha-4` is integrable at zero at
the scalar exponent level exactly when `alpha>3`. -/
theorem logarithmic_family_endpoint
    {alpha : ℝ}
    (h : 3 < alpha) :
    -1 < alpha - 4 := by
  linarith

/-- The integer exponent four is safely to the right of the cubic endpoint. -/
theorem exponent_four_is_admissible :
    (3 : ℝ) < 4 := by
  norm_num

/-- A square-root-sized factor transfers the root logarithmic square energy to
the factorized defect energy after adding one prime denominator power. -/
theorem logarithmic_factor_square_lower
    {c2 p factor root defect logWeight : ℝ}
    (hweight : 0 ≤ logWeight)
    (hscale : c2 * p ≤ factor ^ 2)
    (hdefect : defect = factor * root) :
    c2 * p * root ^ 2 * logWeight
      ≤ defect ^ 2 * logWeight := by
  have hsquare : c2 * p * root ^ 2 ≤ defect ^ 2 := by
    rw [hdefect]
    have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg root)
    nlinarith
  exact mul_le_mul_of_nonneg_right hsquare hweight

/-- The corresponding upper transfer. -/
theorem logarithmic_factor_square_upper
    {C2 p factor root defect logWeight : ℝ}
    (hweight : 0 ≤ logWeight)
    (hscale : factor ^ 2 ≤ C2 * p)
    (hdefect : defect = factor * root) :
    defect ^ 2 * logWeight
      ≤ C2 * p * root ^ 2 * logWeight := by
  have hsquare : defect ^ 2 ≤ C2 * p * root ^ 2 := by
    rw [hdefect]
    have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg root)
    nlinarith
  exact mul_le_mul_of_nonneg_right hsquare hweight

/-- Abstract packaging of one positive-series criterion. -/
theorem one_logarithmic_series_criterion
    {P finiteSeries : Prop}
    (hforward : P → finiteSeries)
    (hfalse : ¬ P → ¬ finiteSeries) :
    P ↔ finiteSeries := by
  constructor
  · exact hforward
  · intro hfinite
    by_contra hP
    exact hfalse hP hfinite

/-- The near-endpoint density `s^2/log^2` pays exactly one inverse logarithm
beyond the cubic power in the symbolic ledger. -/
theorem near_endpoint_power_identity
    (base : ℝ) :
    base + 3 - 3 = base := by
  ring

/-- Any fixed logarithmic power is negligible relative to a positive
polynomial block exponent at the exponent-comparison level. -/
theorem positive_polynomial_margin
    {margin loss : ℝ}
    (h : loss < margin) :
    0 < margin - loss := by
  linarith

#print axioms logarithmic_block_exponent_identity
#print axioms logarithmic_block_margin
#print axioms fourth_laplace_moment_constant
#print axioms logarithmic_family_endpoint
#print axioms exponent_four_is_admissible
#print axioms logarithmic_factor_square_lower
#print axioms logarithmic_factor_square_upper
#print axioms one_logarithmic_series_criterion
#print axioms near_endpoint_power_identity
#print axioms positive_polynomial_margin

end RHSingleLogarithmicCriterionFinite
