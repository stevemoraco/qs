import Mathlib

/-!
# Round 213 Hodge K-theory finite firewalls

This file formalizes only finite logical, exponent and dimension countermodels.
It does not formalize topological or algebraic K-theory, dg categories, Hodge
structures, perfect complexes, semiregularity, Serre duality, Chow groups, or
the Hodge conjecture.
-/

namespace Millennium
namespace Round213Hodge

/-- A deliberately tiny algebraic-class map whose image contains only one of
two ambient topological classes. -/
def algebraicClassMap (_u : Unit) : Bool := false

/-- Every ambient class is declared Hodge in this logical shadow. -/
def IsTopologicalHodge (_b : Bool) : Prop := True

/-- An ambient topological Hodge class need not have an algebraic preimage
without a separate surjectivity theorem. -/
theorem exists_hodge_topological_class_without_algebraic_lift :
    ∃ b : Bool,
      IsTopologicalHodge b ∧ ¬ ∃ u : Unit, algebraicClassMap u = b := by
  refine ⟨true, trivial, ?_⟩
  intro h
  rcases h with ⟨u, hu⟩
  cases u
  simp [algebraicClassMap] at hu

/-- Algebraic nonnegative Bott-exponent shadow. -/
def nonnegativeBottExponent (n : ℕ) : ℤ := Int.ofNat n

/-- The inverse Bott exponent exists in the localized integer exponent group
but has no nonnegative preimage. -/
theorem inverse_bott_exponent_has_no_unlocalized_preimage :
    ¬ ∃ n : ℕ, nonnegativeBottExponent n = -1 := by
  intro h
  rcases h with ⟨n, hn⟩
  simp [nonnegativeBottExponent] at hn

/-- A scalar semiregularity-shadow map with a nontrivial kernel. -/
def semiregularityShadow (v : ℚ × ℚ) : ℚ := v.1

/-- A nonzero obstruction can have zero semiregularity image when the map is
not injective. -/
theorem nonzero_obstruction_in_semiregularity_kernel :
    semiregularityShadow (0, 1) = 0 ∧
      ((0, 1) : ℚ × ℚ) ≠ (0, 0) := by
  norm_num [semiregularityShadow]

/-- Vanishing of a semiregularity image does not universally force the
obstruction itself to vanish. -/
theorem zero_semiregularity_image_does_not_force_zero_obstruction :
    ¬ (∀ v : ℚ × ℚ,
      semiregularityShadow v = 0 → v = (0, 0)) := by
  intro h
  exact nonzero_obstruction_in_semiregularity_kernel.2
    (h (0, 1) nonzero_obstruction_in_semiregularity_kernel.1)

/-- Scalar connectivity condition at one positive cohomological degree. -/
def ConnectiveAtPositiveDegree
    (degree topExtDim : ℕ) : Prop :=
  0 < degree → topExtDim = 0

/-- Finite dimension shadow of Serre duality: if top self-Ext has the same
positive dimension as endomorphisms, it contradicts connectivity in a positive
degree. -/
theorem serre_duality_shadow_obstructs_connectivity
    (degree homDim topExtDim : ℕ)
    (hdegree : 0 < degree)
    (hidentity : 0 < homDim)
    (hserre : topExtDim = homDim) :
    ¬ ConnectiveAtPositiveDegree degree topExtDim := by
  intro hconnective
  have hzero : topExtDim = 0 := hconnective hdegree
  omega

/-- The one-dimensional identity/top-Ext model already obstructs
connectivity at every positive Calabi--Yau dimension. -/
theorem one_dimensional_serre_shadow_not_connective
    (degree : ℕ) (hdegree : 0 < degree) :
    ¬ ConnectiveAtPositiveDegree degree 1 := by
  exact serre_duality_shadow_obstructs_connectivity
    degree 1 1 hdegree (by omega) rfl

/-- A uniform lift function gives pointwise lifts; the converse is not supplied
by this implication. -/
theorem uniform_lift_implies_pointwise_lifts
    {Index Algebraic Topological : Type*}
    (classAt : Index → Topological)
    (realize : Algebraic → Topological)
    (lift : Index → Algebraic)
    (hlift : ∀ i, realize (lift i) = classAt i) :
    ∀ i, ∃ a, realize a = classAt i := by
  intro i
  exact ⟨lift i, hlift i⟩

#print axioms exists_hodge_topological_class_without_algebraic_lift
#print axioms inverse_bott_exponent_has_no_unlocalized_preimage
#print axioms nonzero_obstruction_in_semiregularity_kernel
#print axioms zero_semiregularity_image_does_not_force_zero_obstruction
#print axioms serre_duality_shadow_obstructs_connectivity
#print axioms one_dimensional_serre_shadow_not_connective
#print axioms uniform_lift_implies_pointwise_lifts

end Round213Hodge
end Millennium
