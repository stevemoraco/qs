import Mathlib

/-!
# Stable-plane work-blindness and twist firewall

Finite real algebra only.  These lemmas isolate the exact biaxial-strain
countermodel behind the Type-I fixed-lag Navier--Stokes audit:

* the trace-free biaxial strain `diag(a,a,-2a)` gives the same maximal work to
  every unit direction in its positive two-plane;
* the Rayleigh deficit sees only the normal component and is blind to the
  in-plane angle;
* the biaxial part produces no in-plane turning;
* any in-plane turning must therefore be carried by a residual term.

They do **not** formalize Navier--Stokes, Yu's filtered operators, the
Lei--Ren--Tian cone theorem, ancient solutions, or any Millennium conclusion.
-/

namespace NSStablePlaneTwistFirewall

/-- Quadratic work of the trace-free biaxial strain `diag(a,a,-2a)`. -/
def biaxialWork (a x y z : ℝ) : ℝ :=
  a * x^2 + a * y^2 - 2 * a * z^2

/-- On the unit sphere the biaxial Rayleigh deficit is exactly the squared
normal component times `3a`.  Hence it contains no in-plane angular data. -/
theorem biaxial_work_unit_identity
    (a x y z : ℝ)
    (hunit : x^2 + y^2 + z^2 = 1) :
    a - biaxialWork a x y z = 3 * a * z^2 := by
  unfold biaxialWork
  calc
    a - (a * x^2 + a * y^2 - 2 * a * z^2) =
        a * (1 - (x^2 + y^2 + z^2)) + 3 * a * z^2 := by ring
    _ = 3 * a * z^2 := by rw [hunit]; ring

/-- Every unit direction in the positive plane has the same top-eigenvalue
work `a`. -/
theorem equatorial_direction_has_maximal_biaxial_work
    (a x y : ℝ)
    (hunit : x^2 + y^2 = 1) :
    biaxialWork a x y 0 = a := by
  unfold biaxialWork
  calc
    a * x^2 + a * y^2 - 2 * a * 0^2 = a * (x^2 + y^2) := by ring
    _ = a := by rw [hunit]; ring

/-- A quarter-turn inside the positive plane leaves the biaxial work exactly
unchanged. -/
theorem quarter_turn_preserves_biaxial_work
    (a x y z : ℝ) :
    biaxialWork a (-y) x z = biaxialWork a x y z := by
  unfold biaxialWork
  ring

/-- The two orthogonal coordinate directions in the positive plane both attain
maximal biaxial work. -/
theorem orthogonal_equatorial_maximizers (a : ℝ) :
    biaxialWork a 1 0 0 = a ∧
    biaxialWork a 0 1 0 = a ∧
    (1 : ℝ) * 0 + 0 * 1 = 0 := by
  constructor
  · norm_num [biaxialWork]
  constructor
  · norm_num [biaxialWork]
  · norm_num

/-- If `ξ=(x,y,0)` lies in the positive plane and
`τ=(-y,x,0)` is its in-plane quarter-turn, then the biaxial strain contributes
zero tangential turning. -/
theorem biaxial_inplane_turning_zero
    (a x y : ℝ) :
    (-y) * (a * x) + x * (a * y) = 0 := by
  ring

/-- Exact orthogonal decomposition of a residual vector into the in-plane
radial and tangential directions determined by a unit `(x,y)`. -/
theorem residual_turning_pythagorean
    (x y r₁ r₂ : ℝ)
    (hunit : x^2 + y^2 = 1) :
    (-y * r₁ + x * r₂)^2 + (x * r₁ + y * r₂)^2 = r₁^2 + r₂^2 := by
  calc
    (-y * r₁ + x * r₂)^2 + (x * r₁ + y * r₂)^2 =
        (x^2 + y^2) * (r₁^2 + r₂^2) := by ring
    _ = r₁^2 + r₂^2 := by rw [hunit]; ring

/-- The squared in-plane turning supplied by a residual is bounded by the
squared residual amplitude in that plane. -/
theorem residual_controls_inplane_turning
    (x y r₁ r₂ : ℝ)
    (hunit : x^2 + y^2 = 1) :
    (-y * r₁ + x * r₂)^2 ≤ r₁^2 + r₂^2 := by
  have h := residual_turning_pythagorean x y r₁ r₂ hunit
  have hnonneg : 0 ≤ (x * r₁ + y * r₂)^2 := sq_nonneg _
  nlinarith

/-- Near-maximal biaxial work controls only the normal component. -/
theorem near_maximal_biaxial_work_controls_normal
    (a x y z ε : ℝ)
    (hunit : x^2 + y^2 + z^2 = 1)
    (hwork : a - biaxialWork a x y z ≤ ε) :
    3 * a * z^2 ≤ ε := by
  rw [biaxial_work_unit_identity a x y z hunit] at hwork
  exact hwork

#print axioms biaxial_work_unit_identity
#print axioms equatorial_direction_has_maximal_biaxial_work
#print axioms quarter_turn_preserves_biaxial_work
#print axioms orthogonal_equatorial_maximizers
#print axioms biaxial_inplane_turning_zero
#print axioms residual_turning_pythagorean
#print axioms residual_controls_inplane_turning
#print axioms near_maximal_biaxial_work_controls_normal

end NSStablePlaneTwistFirewall
