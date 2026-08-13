import Mathlib

namespace RHSingleDampedCriterionFinite

/-- A false-RH bad block retains a positive polynomial exponent after the
fixed subpower damping and two logarithmic denominators whenever
`3*epsilon<2*delta`. -/
theorem fixed_damped_block_margin
    {delta epsilon : ℝ}
    (h : 3 * epsilon < 2 * delta) :
    0 < 2 * delta - 3 * epsilon := by
  linarith

/-- The exact polynomial exponent of the fixed-damping root-energy block. -/
theorem fixed_damped_block_exponent_identity
    (delta epsilon : ℝ) :
    (1 - epsilon) + (2 * delta - 2 * epsilon) - 1
      = 2 * delta - 3 * epsilon := by
  ring

/-- A factor whose square is comparable to `p` transfers the root square
energy to the factorized defect energy with one additional denominator power. -/
theorem factorized_fixed_weight_lower
    {c2 p factor root defect weight : ℝ}
    (hweight : 0 ≤ weight)
    (hscale : c2 * p ≤ factor ^ 2)
    (hdefect : defect = factor * root) :
    c2 * p * root ^ 2 * weight ≤ defect ^ 2 * weight := by
  have hsquare : c2 * p * root ^ 2 ≤ defect ^ 2 := by
    rw [hdefect]
    have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg root)
    nlinarith
  exact mul_le_mul_of_nonneg_right hsquare hweight

/-- The corresponding fixed-weight upper transfer. -/
theorem factorized_fixed_weight_upper
    {C2 p factor root defect weight : ℝ}
    (hweight : 0 ≤ weight)
    (hscale : factor ^ 2 ≤ C2 * p)
    (hdefect : defect = factor * root) :
    defect ^ 2 * weight ≤ C2 * p * root ^ 2 * weight := by
  have hsquare : defect ^ 2 ≤ C2 * p * root ^ 2 := by
    rw [hdefect]
    have hmul := mul_le_mul_of_nonneg_right hscale (sq_nonneg root)
    nlinarith
  exact mul_le_mul_of_nonneg_right hsquare hweight

/-- The scalar cancellation behind the weighted Hardy test:
`(2 exp(-z)/z) * (2 z exp z)=4` for nonzero `z`. -/
theorem hardy_weight_product
    {z : ℝ}
    (hz : z ≠ 0) :
    (2 * Real.exp (-z) / z) * (2 * z * Real.exp z) = 4 := by
  have hexp : Real.exp (-z) * Real.exp z = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp [hz]
  nlinarith

/-- A strict contraction with norm at most `1/sqrt 2` has a positive
Neumann-series margin. -/
theorem dyadic_fixed_weight_margin :
    0 < 1 - 1 / Real.sqrt 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt 2 := lt_trans (by norm_num) hsqrt
  have hone : 1 / Real.sqrt 2 < 1 := by
    exact (div_lt_one hsqrt_pos).2 hsqrt
  linarith

/-- Abstract logical packaging of the single-series criterion. -/
theorem single_series_criterion
    {P finiteSeries : Prop}
    (hforward : P → finiteSeries)
    (hreverse : ¬ P → ¬ finiteSeries) :
    P ↔ finiteSeries := by
  constructor
  · exact hforward
  · intro hfinite
    by_contra hP
    exact hreverse hP hfinite

/-- The logarithmic Hardy denominator is one power beyond the undamped target
in the elementary exponent ledger. -/
theorem logarithmic_hardy_denominator_shift
    (base : ℝ) :
    base + 1 - 1 = base := by
  ring

/-- Choosing any positive epsilon below `2 delta / 3` leaves the fixed-damping
bad-block margin positive. -/
theorem choose_fixed_damped_loss
    {delta epsilon : ℝ}
    (hepsilon : epsilon < 2 * delta / 3) :
    0 < 2 * delta - 3 * epsilon := by
  linarith

#print axioms fixed_damped_block_margin
#print axioms fixed_damped_block_exponent_identity
#print axioms factorized_fixed_weight_lower
#print axioms factorized_fixed_weight_upper
#print axioms hardy_weight_product
#print axioms dyadic_fixed_weight_margin
#print axioms single_series_criterion
#print axioms logarithmic_hardy_denominator_shift
#print axioms choose_fixed_damped_loss

end RHSingleDampedCriterionFinite
