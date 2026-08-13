import Mathlib

namespace RHLocalDipBank

/-- Algebraic core of the convex-recovery/local-dip bound.
If a value lies above the quadratic model

`base - J*t + (kappa/2)*t^2`,

then the model can fall below `base` by at most `J^2/(2*kappa)`.
The conclusion is polynomialized to avoid division. -/
theorem quadratic_local_dip_bound
    {base value J kappa t : ℝ}
    (hkappa : 0 < kappa)
    (hmodel : base - J * t + (kappa / 2) * t ^ 2 ≤ value) :
    2 * kappa * base - J ^ 2 ≤ 2 * kappa * value := by
  have hsquare : 0 ≤ (kappa * t - J) ^ 2 := sq_nonneg (kappa * t - J)
  nlinarith

/-- Equivalent divided form of the local-dip theorem. -/
theorem quadratic_local_dip_bound_div
    {base value J kappa t : ℝ}
    (hkappa : 0 < kappa)
    (hmodel : base - J * t + (kappa / 2) * t ^ 2 ≤ value) :
    base - J ^ 2 / (2 * kappa) ≤ value := by
  have hpoly := quadratic_local_dip_bound hkappa hmodel
  have hk2 : 0 < 2 * kappa := by positivity
  apply (le_div_iff₀ hk2).mp
  field_simp [ne_of_gt hkappa]
  nlinarith

/-- The exact half-knot jump has quadratic size after the local-dip estimate:
if `J = 2*L/x^2`, then `J^2 = 4*L^2/x^4`. -/
theorem half_knot_jump_square
    {J L x : ℝ}
    (hJ : J = 2 * L / x ^ 2) :
    J ^ 2 = 4 * L ^ 2 / x ^ 4 := by
  rw [hJ]
  ring

#print axioms quadratic_local_dip_bound
#print axioms quadratic_local_dip_bound_div
#print axioms half_knot_jump_square

end RHLocalDipBank
