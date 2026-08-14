import Mathlib

/-!
Finite arithmetic/polynomial shadow of `stevemoraco/RH#500`.

Formalized here only:
* the intersection/fundamental-cycle arithmetic for the forced candidate graph
  `F(-1)--E0(-2)--E1(-3)--Q(-2)`;
* the rational canonical-cycle solution `(10,7,4,2)/3`;
* the determinant-three/canonical-denominator ledger;
* one exact two-parameter binary-cubic order countermodel showing that
  square-zero closed fibre + simple/double boundary + pure-cube collision +
  index `L^13` are algebraically compatible at the finite polynomial level.

NOT formalized:
proximity geometry, the proof that this graph is forced, the moving-A3 analytic
classification, finite-flat Stein factorization, Gorenstein/minimally-elliptic
theory, Miranda/Tschirnhausen bundles, K3 geometry, algebraic cycles, or Hodge
theory. No axiom below carries any such conclusion.
-/

namespace Millennium.Hodge.R3Q1A8C2CoincidentGraphFiniteCore

/-- Binary-cubic discriminant. -/
def cubicDisc (a b c d : ℚ) : ℚ :=
  b^2 * c^2 - 4*a*c^3 - 4*b^3*d - 27*a^2*d^2 + 18*a*b*c*d

/-- The all-ones fundamental-cycle candidate has intersections `(0,0,-1,-1)`
with the chain `(-1,-2,-3,-2)`. -/
theorem fundamental_cycle_intersections :
    (-1 : ℤ) + 1 = 0 ∧
    1 - 2 + 1 = 0 ∧
    1 - 3 + 1 = -1 ∧
    1 - 2 = -1 := by
  norm_num

/-- The rational canonical-cycle coefficients solve `Z_K.E=-K.E` for
`K.E=(1,0,1,0)`. -/
theorem canonical_cycle_equations :
    let f : ℚ := 10/3
    let e0 : ℚ := 7/3
    let e1 : ℚ := 4/3
    let q : ℚ := 2/3
    (-f + e0 = -1) ∧
    (f - 2*e0 + e1 = 0) ∧
    (e0 - 3*e1 + q = -1) ∧
    (e1 - 2*q = 0) := by
  norm_num

/-- Determinant of the tridiagonal intersection matrix `(-1,-2,-3,-2)` is 3.
Written as the continuant recurrence to keep the finite core elementary. -/
theorem intersection_determinant_three :
    let d1 : ℤ := -1
    let d2 : ℤ := (-2) * d1 - 1
    let d3 : ℤ := (-3) * d2 - d1
    let d4 : ℤ := (-2) * d3 - d2
    d4 = 3 := by
  norm_num

/-- The canonical coefficients genuinely have denominator three. -/
theorem canonical_denominator_three :
    (10 : ℚ) / 3 ∉ Set.range (fun z : ℤ => (z : ℚ)) := by
  intro h
  rcases h with ⟨z, hz⟩
  have hz3 : (10 : ℚ) = 3 * (z : ℚ) := by linarith
  have hmod : (10 : ℤ) = 3 * z := by exact_mod_cast hz3
  omega

/-- Fundamental-cycle arithmetic-genus ledger: `Z^2=-2`, `K.Z=2`, hence
`1+(Z^2+K.Z)/2=1`. -/
theorem fundamental_arithmetic_genus_ledger :
    1 + ((-2 : ℚ) + 2) / 2 = 1 := by
  norm_num

/-- Determinant-twisted pullback for the explicit two-parameter local model at
`m=13`. -/
theorem determinant_twisted_pullback_model (L u X Y : ℚ) :
    L^13 * (u * L^26 * X^3 - u*X*Y^2 + Y^3) =
      u * (L^13*X)^3 - u*(L^13*X)*Y^2 + L^13*Y^3 := by
  ring

/-- Normalized discriminant of
`u X^3 - u X Y^2 + L^13 Y^3`. -/
theorem normalized_model_discriminant (L u : ℚ) :
    cubicDisc u 0 (-u) (L^13) = u^2 * (4*u^2 - 27*L^26) := by
  ring_nf [cubicDisc]

/-- Raw discriminant of
`u L^26 X^3 - u X Y^2 + Y^3`. -/
theorem raw_model_discriminant (L u : ℚ) :
    cubicDisc (u*L^26) 0 (-u) 1 =
      L^26 * u^2 * (4*u^2 - 27*L^26) := by
  ring_nf [cubicDisc]

/-- The local model obeys the square-index discriminant law. -/
theorem model_discriminant_index_identity (L u : ℚ) :
    cubicDisc (u*L^26) 0 (-u) 1 =
      L^26 * cubicDisc u 0 (-u) (L^13) := by
  rw [raw_model_discriminant, normalized_model_discriminant]

/-- Generic alpha-boundary raw cubic is simple times doubled. -/
theorem raw_alpha_boundary_factorization (u X Y : ℚ) :
    -u*X*Y^2 + Y^3 = Y^2 * (Y-u*X) := by
  ring

/-- Generic normalized alpha-boundary cubic is reduced when its displayed
linear factors are distinct; here we formalize only the polynomial identity. -/
theorem normalized_alpha_boundary_factorization (u X Y : ℚ) :
    u*X^3 - u*X*Y^2 = u*X*(X-Y)*(X+Y) := by
  ring

/-- At the marked collision `u=0`, the raw cubic is the pure cube `Y^3`. -/
theorem raw_collision_pure_cube (L X Y : ℚ) :
    (0:ℚ) * L^26 * X^3 - 0*X*Y^2 + Y^3 = Y^3 := by
  ring

/-- Exact index-order ledger `2*13=26`. -/
theorem index_order_ledger : 2 * 13 = 26 := by norm_num

#print axioms fundamental_cycle_intersections
#print axioms canonical_cycle_equations
#print axioms intersection_determinant_three
#print axioms canonical_denominator_three
#print axioms fundamental_arithmetic_genus_ledger
#print axioms determinant_twisted_pullback_model
#print axioms normalized_model_discriminant
#print axioms raw_model_discriminant
#print axioms model_discriminant_index_identity
#print axioms raw_alpha_boundary_factorization
#print axioms normalized_alpha_boundary_factorization
#print axioms raw_collision_pure_cube
#print axioms index_order_ledger

end Millennium.Hodge.R3Q1A8C2CoincidentGraphFiniteCore
