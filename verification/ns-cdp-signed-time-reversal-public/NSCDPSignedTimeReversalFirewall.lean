import Mathlib

namespace NSCDPSignedTimeReversalFirewall

/-- Scalar shadow of signed time reversal: if the original equation is
`ut - nu*lap + nonlinear = 0`, then the signed-reversed residual is
`ut + nu*lap + nonlinear = 2*nu*lap`. -/
theorem signed_reversal_residual_identity
    {nu ut lap nonlinear : ℝ}
    (hEquation : ut - nu * lap + nonlinear = 0) :
    ut + nu * lap + nonlinear = 2 * nu * lap := by
  linarith

/-- If the projected force is `-2*nu*lap`, its magnitude is exactly twice
viscosity times the Laplacian magnitude. -/
theorem force_abs_eq_twice_viscosity_laplacian
    {nu lap force : ℝ}
    (hnu : 0 ≤ nu)
    (hforce : force = -2 * nu * lap) :
    |force| = 2 * nu * |lap| := by
  calc
    |force| = |-2 * nu * lap| := by rw [hforce]
    _ = |-2| * |nu| * |lap| := by rw [abs_mul, abs_mul]
    _ = 2 * nu * |lap| := by norm_num [abs_of_nonneg hnu]

/-- A pointwise projected-force budget transfers to the Laplacian budget. -/
theorem force_budget_bounds_laplacian
    {nu lap force budget : ℝ}
    (hnu : 0 < nu)
    (hforce : force = -2 * nu * lap)
    (hbudget : |force| ≤ budget) :
    |lap| ≤ budget / (2 * nu) := by
  have habs := force_abs_eq_twice_viscosity_laplacian
    (lap := lap) (force := force) (le_of_lt hnu) hforce
  rw [habs] at hbudget
  have h2nu : 0 < 2 * nu := by positivity
  apply (le_div_iff₀ h2nu).2
  simpa [mul_comm] using hbudget

/-- With nonzero viscosity, zero projected force forces zero Laplacian under
signed reversal. -/
theorem zero_force_forces_zero_laplacian
    {nu lap force : ℝ}
    (hnu : nu ≠ 0)
    (hforce : force = -2 * nu * lap)
    (hzero : force = 0) :
    lap = 0 := by
  have hmul : (-2 * nu) * lap = 0 := by
    calc
      (-2 * nu) * lap = force := by linarith
      _ = 0 := hzero
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hnu)

/-- Exact residual for the general scalar amplitude/time transform
`v(t)=a(t)u(phi(t))`. -/
theorem amplitude_time_residual_decomposition
    {ap a r nu u ut lap nonlinear : ℝ}
    (hEquation : ut - nu * lap + nonlinear = 0) :
    ap * u + a * r * ut - nu * a * lap + a ^ 2 * nonlinear =
      ap * u + nu * a * (r - 1) * lap + a * (a - r) * nonlinear := by
  have hut : ut = nu * lap - nonlinear := by linarith
  rw [hut]
  ring

/-- The Euler-signed simple reversal is the specialization `a=r=-1` of the
general amplitude-time residual. -/
theorem simple_signed_reversal_specialization
    {nu u ut lap nonlinear : ℝ}
    (hEquation : ut - nu * lap + nonlinear = 0) :
    0 * u + (-1) * (-1) * ut - nu * (-1) * lap + (-1 : ℝ) ^ 2 * nonlinear =
      2 * nu * lap := by
  have hres := amplitude_time_residual_decomposition
    (ap := 0) (a := (-1 : ℝ)) (r := (-1 : ℝ))
    (nu := nu) (u := u) (ut := ut) (lap := lap) (nonlinear := nonlinear)
    hEquation
  norm_num at hres ⊢
  linarith

#print axioms signed_reversal_residual_identity
#print axioms force_abs_eq_twice_viscosity_laplacian
#print axioms force_budget_bounds_laplacian
#print axioms zero_force_forces_zero_laplacian
#print axioms amplitude_time_residual_decomposition
#print axioms simple_signed_reversal_specialization

end NSCDPSignedTimeReversalFirewall
