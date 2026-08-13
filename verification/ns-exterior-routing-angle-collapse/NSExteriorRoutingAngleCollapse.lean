import Mathlib

/-!
# Exterior-routing angle-collapse finite core

This file formalizes only the scalar algebra used in the audit of the
Navier--Stokes equal-shell exterior-routing idea.

It does not define the Navier--Stokes equations, assert a PDE embedding, or
carry any Clay conclusion in an assumption.
-/

namespace NSExteriorRoutingAngleCollapse

/-- One coordinate of the two exterior outputs has tripled sum. -/
theorem exterior_sum_coordinate (p q : ℝ) :
    (2 * p + q) + (p + 2 * q) = 3 * (p + q) := by
  ring

/-- One coordinate of the two exterior outputs has unchanged difference. -/
theorem exterior_difference_coordinate (p q : ℝ) :
    (2 * p + q) - (p + 2 * q) = p - q := by
  ring

/-- Diagonalized form of one exterior-routing step. -/
theorem exterior_diagonalized_step (s d : ℝ) :
    2 * ((s + d) / 2) + ((s - d) / 2) = (3 * s + d) / 2 ∧
      ((s + d) / 2) + 2 * ((s - d) / 2) = (3 * s - d) / 2 := by
  constructor <;> ring

/-- If `pp`, `qq`, and `pq` denote the two input squared norms and their
inner product, the squared-norm difference of the exterior pair is exactly
three times the original squared-norm difference. -/
theorem exterior_norm_sq_difference (pp qq pq : ℝ) :
    (4 * pp + qq + 4 * pq) - (pp + 4 * qq + 4 * pq) =
      3 * (pp - qq) := by
  ring

/-- Equal input shells therefore produce equal exterior shells. -/
theorem exterior_equal_shell
    {pp qq pq : ℝ} (h : pp = qq) :
    4 * pp + qq + 4 * pq = pp + 4 * qq + 4 * pq := by
  nlinarith

/-- Cleared-denominator form of the fixed-chord coupling ceiling:
`S D / sqrt(S²+D²)` has magnitude at most `|D|`. -/
theorem fixed_chord_coupling_sq_cleared (S D : ℝ) :
    (S * D) ^ 2 ≤ D ^ 2 * (S ^ 2 + D ^ 2) := by
  nlinarith [sq_nonneg (D ^ 2)]

/-- Cleared form of `c/(1+c²) ≤ 1/2` for `c ≥ 0`. -/
theorem relay_prefactor_le_half_cleared
    {c : ℝ} (hc : 0 ≤ c) :
    2 * c ≤ 1 + c ^ 2 := by
  nlinarith [sq_nonneg (c - 1)]

/-- Once a nonnegative coupling is bounded by half a fixed chord, a quadratic
viscous rate dominates whenever the displayed finite threshold holds. -/
theorem viscosity_dominates_fixed_chord
    {lam R nu N D : ℝ}
    (hlam : 0 ≤ lam)
    (hR : 0 ≤ R)
    (hnu : 0 < nu)
    (hcoup : 2 * lam ≤ D)
    (hlarge : D * R < 2 * nu * N ^ 2) :
    lam * R < nu * N ^ 2 := by
  have hmul : 0 ≤ (D - 2 * lam) * R :=
    mul_nonneg (sub_nonneg.mpr hcoup) hR
  nlinarith

#print axioms exterior_sum_coordinate
#print axioms exterior_difference_coordinate
#print axioms exterior_diagonalized_step
#print axioms exterior_norm_sq_difference
#print axioms exterior_equal_shell
#print axioms fixed_chord_coupling_sq_cleared
#print axioms relay_prefactor_le_half_cleared
#print axioms viscosity_dominates_fixed_chord

end NSExteriorRoutingAngleCollapse
