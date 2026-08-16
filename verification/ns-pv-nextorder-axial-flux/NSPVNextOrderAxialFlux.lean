import Mathlib

/-!
# RSS next-order axial-flux finite firewall

Finite linear algebra only.

For a rotated self-similar Navier--Stokes next-order stress coefficient,
the human PDE argument shows that divergence-free sphere-flux constancy plus
corrected rotation covariance makes the flux vector fixed by every rotation
about the RSS axis.  A single quarter-turn is already enough to force the two
horizontal components to vanish.

This file formalizes only that representation-theoretic core and the sharp
counterexample that a nonzero axial component survives.  It does not formalize
stress tensors, the divergence theorem, RSS asymptotics, Navier--Stokes, or any
Millennium statement.
-/

namespace NSPVNextOrderAxialFlux

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Quarter-turn about the third coordinate axis. -/
def quarterTurn (v : Vec3) : Vec3 :=
  ⟨-v.y, v.x, v.z⟩

/-- A vector lies on the rotation axis. -/
def IsAxial (v : Vec3) : Prop :=
  v.x = 0 ∧ v.y = 0

/-- A vector fixed by one quarter-turn has no horizontal component. -/
theorem quarterTurn_fixed_implies_axial
    (v : Vec3) (h : quarterTurn v = v) : IsAxial v := by
  have hx : -v.y = v.x := congrArg Vec3.x h
  have hy : v.x = v.y := congrArg Vec3.y h
  constructor <;> linarith

/-- Every axial vector is fixed by the quarter-turn. -/
theorem axial_implies_quarterTurn_fixed
    (v : Vec3) (h : IsAxial v) : quarterTurn v = v := by
  rcases v with ⟨x, y, z⟩
  change x = 0 ∧ y = 0 at h
  rcases h with ⟨hx, hy⟩
  subst x
  subst y
  simp [quarterTurn]

/-- Exact finite characterization of the fixed subspace. -/
theorem quarterTurn_fixed_iff_axial (v : Vec3) :
    quarterTurn v = v ↔ IsAxial v := by
  constructor
  · exact quarterTurn_fixed_implies_axial v
  · exact axial_implies_quarterTurn_fixed v

/-- Symmetry alone does not force the axial coefficient to vanish. -/
theorem nonzero_axial_fixed_counterexample :
    ∃ v : Vec3, quarterTurn v = v ∧ v.z ≠ 0 := by
  refine ⟨⟨0, 0, 1⟩, ?_, by norm_num⟩
  simp [quarterTurn]

/-- Therefore a fixed vector need not be the zero vector. -/
theorem fixed_does_not_imply_zero_vector :
    ¬ (∀ v : Vec3, quarterTurn v = v → v = ⟨0, 0, 0⟩) := by
  intro h
  have hfix : quarterTurn (⟨0, 0, 1⟩ : Vec3) = ⟨0, 0, 1⟩ := by
    simp [quarterTurn]
  have hz := h ⟨0, 0, 1⟩ hfix
  have : (1 : ℝ) = 0 := congrArg Vec3.z hz
  norm_num at this

#print axioms quarterTurn_fixed_implies_axial
#print axioms axial_implies_quarterTurn_fixed
#print axioms quarterTurn_fixed_iff_axial
#print axioms nonzero_axial_fixed_counterexample
#print axioms fixed_does_not_imply_zero_vector

end NSPVNextOrderAxialFlux
