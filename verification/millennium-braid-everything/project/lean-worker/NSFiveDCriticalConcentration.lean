import Mathlib

/-!
# Five-dimensional critical concentration obstruction

This file formalizes two finite cores of a compactness audit for the lifted
axisymmetric Navier--Stokes energy class.

For a parabolic bump

`G_λ(t,x) = λ^a φ(λ x) ψ(λ^2 t)`

in spatial dimension `d`, the scaling exponent of

* `sup_t ‖G_λ(t)‖_2^2` is `2a-d`;
* `∫∫ |∇G_λ|^2` is `2(a+1)-d-2`;
* `∫∫ |G_λ|^p` is `pa-d-2`;
* `∫∫ |G_λ|^2` is `2a-d-2`.

At `d=5`, `a=5/2`, and `p=14/5`, the first three exponents are zero while
the spacetime `L^2` exponent is `-2`.  Thus the energy class and the critical
`L^(14/5)` norm can remain fixed while strong local spacetime `L^2` tends to
zero.

The file also records the pure quantifier obstruction: pointwise existence of
a profile-dependent small radius does not imply one radius works uniformly for
all profiles.

No Navier--Stokes PDE statement is formalized here.
-/

namespace NSFiveDCriticalConcentration

/-- Spatial `L²` energy is invariant for amplitude exponent `5/2` in five
space dimensions. -/
theorem spatial_l2_exponent :
    2 * ((5 : ℚ) / 2) - 5 = 0 := by
  norm_num

/-- The spacetime gradient-energy exponent is also critical. -/
theorem gradient_l2_spacetime_exponent :
    2 * (((5 : ℚ) / 2) + 1) - 5 - 2 = 0 := by
  norm_num

/-- The parabolic Sobolev exponent `14/5` is exactly critical in dimension
five for the energy amplitude `5/2`. -/
theorem critical_fourteen_fifths_exponent :
    ((14 : ℚ) / 5) * ((5 : ℚ) / 2) - 5 - 2 = 0 := by
  norm_num

/-- In contrast, the spacetime `L²` norm gains two inverse powers of the
concentration parameter. -/
theorem spacetime_l2_exponent :
    2 * ((5 : ℚ) / 2) - 5 - 2 = -2 := by
  norm_num

/-- The critical exponent is uniquely forced by parabolic scaling once the
energy amplitude is fixed. -/
theorem critical_exponent_unique {p : ℚ}
    (h : p * ((5 : ℚ) / 2) - 5 - 2 = 0) :
    p = (14 : ℚ) / 5 := by
  linarith

/-- A discrete model of a radius that is small enough for a given profile.
Larger indices represent smaller radii. -/
def radiusWorks (profile radiusIndex : ℕ) : Prop :=
  profile < radiusIndex

/-- Every individual profile admits some sufficiently small radius. -/
theorem pointwise_profile_dependent_radius :
    ∀ profile : ℕ, ∃ radiusIndex : ℕ,
      radiusWorks profile radiusIndex := by
  intro profile
  exact ⟨profile + 1, Nat.lt_succ_self profile⟩

/-- No single radius index works for every profile.  This is the exact
quantifier gap between pointwise absolute continuity and uniform
equi-integrability. -/
theorem no_uniform_radius :
    ¬ ∃ radiusIndex : ℕ, ∀ profile : ℕ,
      radiusWorks profile radiusIndex := by
  rintro ⟨radiusIndex, h⟩
  exact (Nat.lt_irrefl radiusIndex) (h radiusIndex)

/-- The pointwise radius theorem cannot be upgraded to a uniform one. -/
theorem pointwise_does_not_imply_uniform :
    (∀ profile : ℕ, ∃ radiusIndex : ℕ,
      radiusWorks profile radiusIndex) ∧
    ¬ (∃ radiusIndex : ℕ, ∀ profile : ℕ,
      radiusWorks profile radiusIndex) := by
  exact ⟨pointwise_profile_dependent_radius, no_uniform_radius⟩

#print axioms spatial_l2_exponent
#print axioms gradient_l2_spacetime_exponent
#print axioms critical_fourteen_fifths_exponent
#print axioms spacetime_l2_exponent
#print axioms critical_exponent_unique
#print axioms pointwise_profile_dependent_radius
#print axioms no_uniform_radius
#print axioms pointwise_does_not_imply_uniform

end NSFiveDCriticalConcentration
