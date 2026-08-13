import Mathlib

namespace RHConcavePhaseCriterionFinite

/-- Scalar core of the concave-phase Hardy miracle. If the target tail is at
most `d*w` and the inverse-source primitive is at most `1/(d*w)`, their testing
product is at most one. -/
theorem phase_hardy_product_le_one
    {tail inverse d w : ℝ}
    (hd : 0 < d)
    (hw : 0 < w)
    (htail : tail ≤ d * w)
    (hinverse : inverse ≤ 1 / (d * w))
    (htail0 : 0 ≤ tail)
    (hinverse0 : 0 ≤ inverse) :
    tail * inverse ≤ 1 := by
  have hdw : 0 < d * w := mul_pos hd hw
  have h₁ : tail * inverse ≤ (d * w) * inverse :=
    mul_le_mul_of_nonneg_right htail hinverse0
  have h₂ : (d * w) * inverse ≤ (d * w) * (1 / (d * w)) :=
    mul_le_mul_of_nonneg_left hinverse hdw.le
  calc
    tail * inverse ≤ (d * w) * inverse := h₁
    _ ≤ (d * w) * (1 / (d * w)) := h₂
    _ = 1 := by field_simp

/-- For the power phase `phi(y)=y^beta`, the squared derivative contributes
logarithmic exponent `-2(1-beta)`. -/
theorem power_phase_compensation_exponent
    (beta : ℝ) :
    2 * (beta - 1) = -2 * (1 - beta) := by
  ring

/-- The square-root phase is the special case with exactly one inverse power
of logarithmic height. -/
theorem square_root_phase_compensation :
    2 * ((1 : ℝ) / 2 - 1) = -1 := by
  norm_num

/-- For a phase exponent arbitrarily close to one, the generic logarithmic
compensation exponent is arbitrarily close to zero. -/
theorem near_linear_power_compensation
    {beta eta : ℝ}
    (hbeta : 1 - eta / 2 < beta) :
    2 * (1 - beta) < eta := by
  linarith

/-- Algebraic formula for the derivative of the near-power phase `y/log y`,
once `L=log y` is supplied by the analytic layer. -/
theorem near_power_derivative_algebra
    {y L : ℝ}
    (hy : y ≠ 0)
    (hL : L ≠ 0) :
    1 / L - y * (1 / y) / L ^ 2 = (L - 1) / L ^ 2 := by
  field_simp [hy, hL]
  ring

/-- The false-RH block polynomial margin remains positive after any fixed
sublinear phase and derivative losses represented by `phaseLoss`, provided the
combined loss is below the polynomial depth. -/
theorem phase_block_margin
    {delta epsilon phaseLoss : ℝ}
    (h : phaseLoss < 2 * delta - 3 * epsilon) :
    0 < 2 * delta - 3 * epsilon - phaseLoss := by
  linarith

/-- The power-phase prime series carries the exact compensation denominator
power `2(1-beta)`. -/
theorem power_phase_denominator_identity
    (beta : ℝ) :
    -2 + 2 * beta = -2 * (1 - beta) := by
  ring

/-- A positive phase derivative gives a positive square compensation. -/
theorem phase_derivative_square_positive
    {d : ℝ}
    (hd : 0 < d) :
    0 < d ^ 2 := sq_pos_of_pos hd

/-- Abstract logic packaging: a source estimate plus a bounded transfer gives
the target estimate. -/
theorem bounded_transfer_forward
    {sourceFinite targetFinite : Prop}
    (hsource : sourceFinite)
    (htransfer : sourceFinite → targetFinite) :
    targetFinite := htransfer hsource

/-- Combining a forward transfer under `P` with a false-case obstruction gives
an exact criterion. -/
theorem transferred_single_series_criterion
    {P sourceFinite targetFinite : Prop}
    (hsource : P → sourceFinite)
    (htransfer : sourceFinite → targetFinite)
    (hfalse : ¬ P → ¬ targetFinite) :
    P ↔ targetFinite := by
  constructor
  · intro hP
    exact htransfer (hsource hP)
  · intro htarget
    by_contra hP
    exact hfalse hP htarget

#print axioms phase_hardy_product_le_one
#print axioms power_phase_compensation_exponent
#print axioms square_root_phase_compensation
#print axioms near_linear_power_compensation
#print axioms near_power_derivative_algebra
#print axioms phase_block_margin
#print axioms power_phase_denominator_identity
#print axioms phase_derivative_square_positive
#print axioms bounded_transfer_forward
#print axioms transferred_single_series_criterion

end RHConcavePhaseCriterionFinite
