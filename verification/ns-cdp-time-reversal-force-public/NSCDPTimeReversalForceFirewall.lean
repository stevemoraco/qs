import Mathlib

namespace NSCDPTimeReversalForceFirewall

/-- Scalar shadow of the exact time-reparametrized residual.
If `ut - linear + nonlinear = 0`, then changing the time speed to `r`
leaves residual `(r-1) * ut`. -/
theorem residual_coefficient_identity
    {r ut linear nonlinear : ℝ}
    (hEquation : ut - linear + nonlinear = 0) :
    r * ut - linear + nonlinear = (r - 1) * ut := by
  linarith

/-- Every nonpositive time speed has magnitude no larger than its residual coefficient. -/
theorem orientation_reversal_coefficient_dominates
    {r : ℝ}
    (hr : r ≤ 0) :
    |r| ≤ |r - 1| := by
  have hr1 : r - 1 ≤ 0 := by linarith
  rw [abs_of_nonpos hr, abs_of_nonpos hr1]
  linarith

/-- Under orientation reversal, the transformed time derivative is bounded by the
projected force residual in every one-dimensional norm shadow. -/
theorem transformed_derivative_bounded_by_force
    {r ut vt force : ℝ}
    (hr : r ≤ 0)
    (hvt : vt = r * ut)
    (hforce : force = (r - 1) * ut) :
    |vt| ≤ |force| := by
  calc
    |vt| = |r| * |ut| := by rw [hvt, abs_mul]
    _ ≤ |r - 1| * |ut| := by
      exact mul_le_mul_of_nonneg_right
        (orientation_reversal_coefficient_dominates hr) (abs_nonneg ut)
    _ = |force| := by rw [hforce, abs_mul]

/-- Any pointwise force budget transfers directly to the reversed time derivative. -/
theorem force_budget_bounds_transformed_derivative
    {r ut vt force budget : ℝ}
    (hr : r ≤ 0)
    (hvt : vt = r * ut)
    (hforce : force = (r - 1) * ut)
    (hbudget : |force| ≤ budget) :
    |vt| ≤ budget := by
  exact le_trans
    (transformed_derivative_bounded_by_force hr hvt hforce)
    hbudget

/-- For the simple reversal `r=-1`, the required force is exactly twice the
transformed time derivative. -/
theorem simple_reversal_force_is_twice_velocity_derivative
    {ut vt force : ℝ}
    (hvt : vt = -ut)
    (hforce : force = -2 * ut) :
    force = 2 * vt := by
  linarith

/-- A zero projected force cannot support nontrivial orientation-reversed evolution. -/
theorem zero_force_forces_static_under_reversal
    {r ut vt force : ℝ}
    (hr : r ≤ 0)
    (hvt : vt = r * ut)
    (hforce : force = (r - 1) * ut)
    (hzero : force = 0) :
    vt = 0 := by
  have hcoeff : r - 1 ≠ 0 := by
    have : r - 1 < 0 := by linarith
    exact ne_of_lt this
  have hmul : (r - 1) * ut = 0 := by
    rw [← hforce]
    exact hzero
  have hut : ut = 0 := (mul_eq_zero.mp hmul).resolve_left hcoeff
  rw [hvt, hut, mul_zero]

#print axioms residual_coefficient_identity
#print axioms orientation_reversal_coefficient_dominates
#print axioms transformed_derivative_bounded_by_force
#print axioms force_budget_bounds_transformed_derivative
#print axioms simple_reversal_force_is_twice_velocity_derivative
#print axioms zero_force_forces_static_under_reversal

end NSCDPTimeReversalForceFirewall
