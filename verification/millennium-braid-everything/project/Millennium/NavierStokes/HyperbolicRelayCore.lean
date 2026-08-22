import Mathlib

/-!
# Hyperbolic relay finite algebra

This file formalizes only the load-bearing finite coefficient identities for the
three-mode relay

  x' = -2 * λ * y * z
  y' =      λ * x * z
  z' =      λ * x * y.

It does not formalize a Navier--Stokes packet embedding, ODE existence, the
closed-form hyperbolic solution, or any Clay Millennium statement.
-/

namespace Millennium.NavierStokes.HyperbolicRelay

/-- The coefficient pattern `(-2,1,1)` conserves quadratic energy. -/
theorem energyDerivative_zero (λ x y z : ℝ) :
    2 * x * (-2 * λ * y * z) +
      2 * y * (λ * x * z) +
      2 * z * (λ * x * y) = 0 := by
  ring

/-- More generally, the quadratic-energy derivative is controlled by the sum
of the three triad coefficients. -/
theorem energyDerivative_general (a b c λ x y z : ℝ) :
    2 * x * (a * λ * y * z) +
      2 * y * (b * λ * x * z) +
      2 * z * (c * λ * x * y) =
        2 * (a + b + c) * λ * x * y * z := by
  ring

/-- The diagonal `y=z` is tangent to the vector field: the derivative of
`y-z` factors by `y-z`. -/
theorem diagonalDifference_factor (λ x y z : ℝ) :
    λ * x * z - λ * x * y = -λ * x * (y - z) := by
  ring

/-- In particular, on the diagonal the difference derivative is zero. -/
theorem diagonalDifference_zero (λ x y : ℝ) :
    λ * x * y - λ * x * y = 0 := by
  ring

/-- On the invariant diagonal, the pump equation is the scalar Riccati form
`x' = λ (x²-R²)` whenever `R²=x²+2y²`. -/
theorem diagonalPump_riccati
    (λ R x y : ℝ) (hR : R ^ 2 = x ^ 2 + 2 * y ^ 2) :
    -2 * λ * y ^ 2 = λ * (x ^ 2 - R ^ 2) := by
  have hx : x ^ 2 - R ^ 2 = -2 * y ^ 2 := by
    nlinarith
  rw [hx]
  ring

/-- The target state `(0,R/√2,R/√2)` has the same formal quadratic energy as
`(R,0,0)`, expressed without introducing square roots. -/
theorem equalSeedTarget_energy
    (R y : ℝ) (hy : 2 * y ^ 2 = R ^ 2) :
    0 ^ 2 + y ^ 2 + y ^ 2 = R ^ 2 := by
  nlinarith

end Millennium.NavierStokes.HyperbolicRelay
