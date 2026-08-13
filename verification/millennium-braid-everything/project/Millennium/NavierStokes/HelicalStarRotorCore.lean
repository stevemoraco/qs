import Mathlib

/-!
# Finite helical star-rotor algebra

This file formalizes only the finite real algebra of the ideal star rotor.
It does not formalize Fourier helical modes, Navier--Stokes, packet closure,
or blow-up.
-/

namespace Millennium.NavierStokes

open Finset

/-- The ideal star-rotor vector field is tangent to Euclidean energy spheres. -/
theorem starRotor_energy_derivative_zero
    {ι : Type*} [Fintype ι]
    (d : ℝ) (c g : ι → ℝ) :
    2 * d * (-∑ j, g j * c j)
      + ∑ j, 2 * c j * (g j * d) = 0 := by
  rw [sum_mul]
  ring_nf
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- A programmed coupling vector `g = G • v` has squared norm `G^2` when
`v` is a unit vector. -/
theorem programmedCoupling_normSq
    {ι : Type*} [Fintype ι]
    (G : ℝ) (v : ι → ℝ)
    (hv : ∑ j, (v j) ^ 2 = 1) :
    ∑ j, (G * v j) ^ 2 = G ^ 2 := by
  calc
    ∑ j, (G * v j) ^ 2 = G ^ 2 * ∑ j, (v j) ^ 2 := by
      simp_rw [mul_pow]
      rw [← mul_sum]
    _ = G ^ 2 := by rw [hv, mul_one]

/-- The quarter-period endpoint has transferred all donor energy into a unit
catalyst profile. -/
theorem quarterPeriod_endpoint_energy
    {ι : Type*} [Fintype ι]
    (d₀ : ℝ) (v : ι → ℝ)
    (hv : ∑ j, (v j) ^ 2 = 1) :
    (0 : ℝ) ^ 2 + ∑ j, (d₀ * v j) ^ 2 = d₀ ^ 2 := by
  simp [programmedCoupling_normSq d₀ v hv]

end Millennium.NavierStokes
