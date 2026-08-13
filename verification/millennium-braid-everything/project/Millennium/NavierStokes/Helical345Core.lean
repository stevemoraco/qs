import Mathlib

/-!
# The `3-4-5` relay coefficient arithmetic

This file verifies only the real/integer arithmetic behind the projected
helical-triad ratio.  It does not formalize helical bases, Fourier analysis,
Leray projection, triad truncation, or the Navier--Stokes equations.
-/

namespace Millennium.NavierStokes.Helical345

/-- The three positive lengths are in arithmetic progression. -/
theorem lengths_arithmetic_progression : (3 : ℤ) + 5 = 2 * 4 := by
  norm_num

/-- Assigning the middle length to the pump gives the relay coefficient triple
`(-2,1,1)` through the cyclic signed-length differences. -/
theorem coefficient_triple :
    ((3 : ℤ) - 5, (5 : ℤ) - 4, (4 : ℤ) - 3) = (-2, 1, 1) := by
  norm_num

/-- The relay coefficients satisfy the quadratic-energy cancellation law. -/
theorem energy_coefficient_sum : (-2 : ℤ) + 1 + 1 = 0 := by
  norm_num

/-- The same coefficients satisfy the signed-length/helicity cancellation for
lengths `(4,3,5)` attached to the variables `(x,y,z)`. -/
theorem helicity_coefficient_sum :
    (-2 : ℤ) * 4 + 1 * 3 + 1 * 5 = 0 := by
  norm_num

/-- The carrier vectors form an exact integer triad. -/
theorem carrier_sum_zero :
    ((3 : ℤ) + 0 + (-3), 0 + 4 + (-4), 0 + 0 + 0) = (0, 0, 0) := by
  norm_num

/-- Their squared Euclidean lengths are exactly `3²`, `4²`, and `5²`. -/
theorem p_squared_length : (3 : ℤ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 3 ^ 2 := by
  norm_num

theorem q_squared_length : (0 : ℤ) ^ 2 + 4 ^ 2 + 0 ^ 2 = 4 ^ 2 := by
  norm_num

theorem k_squared_length : (-3 : ℤ) ^ 2 + (-4) ^ 2 + 0 ^ 2 = 5 ^ 2 := by
  norm_num

end Millennium.NavierStokes.Helical345
