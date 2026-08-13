import Mathlib

/-!
# Navier--Stokes instantaneous-blowup conversion firewall: finite algebra

This file proves only the scalar algebra of time reversal for the
Leray-projected equation.  It does not formalize a PDE solution, regularity,
elliptic estimates, any cited paper, or a Clay statement.

Interpret `du = ν * lap - nonlinear` componentwise as the unforced equation
`∂ₛu = ν Δu - P div (u ⊗ u)`.  For the sign-reversed time reflection
`v(t) = -u(T-t)`, its time derivative is `du`, its Laplacian is `-lap`,
and its quadratic term is unchanged.  The residual is therefore exactly
`2ν Δu`.
-/

namespace NSInstantaneousBlowupClayFirewall

/-- Componentwise residual identity for sign-reversed time reflection. -/
theorem sign_reversed_time_residual
    (ν du lap nonlinear : ℝ)
    (original : du = ν * lap - nonlinear) :
    du - ν * (-lap) + nonlinear = 2 * ν * lap := by
  rw [original]
  ring

/-- Direct sign-reversed time reflection is not an unforced solution whenever
viscosity and the Laplacian component are both nonzero. -/
theorem sign_reversed_time_residual_ne_zero
    (ν du lap nonlinear : ℝ)
    (original : du = ν * lap - nonlinear)
    (hν : ν ≠ 0)
    (hlap : lap ≠ 0) :
    du - ν * (-lap) + nonlinear ≠ 0 := by
  rw [sign_reversed_time_residual ν du lap nonlinear original]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hν) hlap

/-- Without the velocity sign flip, time reflection has a different residual:
both diffusion and the quadratic term are reversed relative to the equation. -/
theorem unsigned_time_residual
    (ν du lap nonlinear : ℝ)
    (original : du = ν * lap - nonlinear) :
    -du - ν * lap + nonlinear = 2 * (nonlinear - ν * lap) := by
  rw [original]
  ring

#print axioms sign_reversed_time_residual
#print axioms sign_reversed_time_residual_ne_zero
#print axioms unsigned_time_residual

end NSInstantaneousBlowupClayFirewall
