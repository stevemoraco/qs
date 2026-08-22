import Mathlib

namespace Millennium.Hodge.LocalAtiyahFerrand

/-- Degree-one homotopy coefficients for the local three-term complex. -/
structure HomotopyData (R : Type*) where
  a0 : R
  a1 : R
  a2 : R
  a3 : R
  c0 : R
  c1 : R
  c2 : R
  c3 : R
  b0 : R
  b1 : R
  b2 : R
  b3 : R

/-- First component of `D₁ h⁻¹ + h⁰ D₀` for
`D₀ = [(-v,u,0,0),(0,0,-z,w)]` and `D₁ = (-u,-v,w,z)`. -/
def boundary0 {R : Type*} [CommRing R]
    (u v w z : R) (h : HomotopyData R) : R :=
  (-u) * h.a0 + (-v) * h.a1 + w * h.a2 + z * h.a3 +
    h.b0 * (-v) + h.b1 * u

/-- Second component of `D₁ h⁻¹ + h⁰ D₀` for the same complex. -/
def boundary1 {R : Type*} [CommRing R]
    (u v w z : R) (h : HomotopyData R) : R :=
  (-u) * h.c0 + (-v) * h.c1 + w * h.c2 + z * h.c3 +
    h.b2 * (-z) + h.b3 * w

/-- BANKER: every degree-two boundary vanishes after evaluating the four
local parameters at the closed point. -/
theorem banker_boundaries_vanish_under_origin_evaluation
    {R S : Type*} [CommRing R] [CommRing S]
    (ev : R →+* S) (u v w z : R) (h : HomotopyData R)
    (hu : ev u = 0) (hv : ev v = 0)
    (hw : ev w = 0) (hz : ev z = 0) :
    ev (boundary0 u v w z h) = 0 ∧
      ev (boundary1 u v w z h) = 0 := by
  constructor <;> simp [boundary0, boundary1, hu, hv, hw, hz]

/-- CRITIC: at the origin, the unit row `(1,0)` is not a degree-two boundary. -/
theorem critic_unit_row_is_not_boundary (h : HomotopyData ℤ) :
    (boundary0 (0 : ℤ) 0 0 0 h, boundary1 (0 : ℤ) 0 0 0 h) ≠ (1, 0) := by
  simp [boundary0, boundary1]

/-- CLEANER: any target row with a nonzero closed-point evaluation is
excluded from the boundary image. -/
theorem cleaner_nonzero_evaluation_obstructs_boundary
    {R S : Type*} [CommRing R] [CommRing S]
    (ev : R →+* S) (u v w z c0 c1 : R) (h : HomotopyData R)
    (hu : ev u = 0) (hv : ev v = 0)
    (hw : ev w = 0) (hz : ev z = 0)
    (hnonzero : ev c0 ≠ 0 ∨ ev c1 ≠ 0) :
    (boundary0 u v w z h, boundary1 u v w z h) ≠ (c0, c1) := by
  intro hpair
  have hb := banker_boundaries_vanish_under_origin_evaluation
    ev u v w z h hu hv hw hz
  have h0 : boundary0 u v w z h = c0 := congrArg Prod.fst hpair
  have h1 : boundary1 u v w z h = c1 := congrArg Prod.snd hpair
  rcases hnonzero with hnonzero | hnonzero
  · apply hnonzero
    rw [← h0]
    exact hb.1
  · apply hnonzero
    rw [← h1]
    exact hb.2

/-- BANKER: the Ferrand conormal equation forces the integer `6t-1`
to have square `73`. -/
theorem banker_ferrand_equation_forces_discriminant_square
    (t : ℤ) (h : 3 * t ^ 2 - t = 6) :
    (6 * t - 1) ^ 2 = 73 := by
  nlinarith

/-- CRITIC: `73` is not a square in the integers. -/
theorem critic_seventy_three_is_not_an_integer_square (y : ℤ) :
    y ^ 2 ≠ 73 := by
  intro hy
  have hlo : -8 ≤ y := by
    by_contra h
    have hle : y ≤ -9 := by omega
    nlinarith [sq_nonneg (y + 9)]
  have hhi : y ≤ 8 := by
    by_contra h
    have hge : 9 ≤ y := by omega
    nlinarith [sq_nonneg (y - 9)]
  have hprod : 0 ≤ (8 - y) * (y + 8) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- CLEANER: no integral primitive class can satisfy the Ferrand-double
Chern equation `3t²-t=6`. -/
theorem cleaner_no_ferrand_integer_solution (t : ℤ) :
    3 * t ^ 2 - t ≠ 6 := by
  intro h
  apply critic_seventy_three_is_not_an_integer_square (6 * t - 1)
  exact banker_ferrand_equation_forces_discriminant_square t h

#print axioms banker_boundaries_vanish_under_origin_evaluation
#print axioms critic_unit_row_is_not_boundary
#print axioms cleaner_nonzero_evaluation_obstructs_boundary
#print axioms banker_ferrand_equation_forces_discriminant_square
#print axioms critic_seventy_three_is_not_an_integer_square
#print axioms cleaner_no_ferrand_integer_solution

end Millennium.Hodge.LocalAtiyahFerrand
