import Mathlib

/-!
# Round 211 rigid-union finite logical firewalls

This file formalizes only finite predicates and a finite maximizer countermodel.
It does not formalize probability measures, compact frame spaces, transfer
coefficients, vorticity, Navier--Stokes solutions, or the Clay problem.
-/

namespace Millennium
namespace Round211NavierStokes

/-- Scalar two-dimensional rigid-family predicate. -/
def Rigid2D (b : Bool) : Prop := b = false

/-- Scalar axisymmetric rigid-family predicate. -/
def RigidAxi (b : Bool) : Prop := b = true

/-- A mixed support containing both rigid points. -/
def MixedSupport (_b : Bool) : Prop := True

/-- Every point of the mixed support lies in the union of the two rigid
families. -/
theorem mixed_support_lies_in_rigid_union :
    ∀ b, MixedSupport b → Rigid2D b ∨ RigidAxi b := by
  intro b hb
  cases b <;> simp [Rigid2D, RigidAxi]

/-- The same mixed support is not contained in the two-dimensional family. -/
theorem mixed_support_not_in_2d :
    ¬ (∀ b, MixedSupport b → Rigid2D b) := by
  intro h
  have hbad := h true trivial
  simp [Rigid2D] at hbad

/-- The same mixed support is not contained in the axisymmetric family. -/
theorem mixed_support_not_in_axi :
    ¬ (∀ b, MixedSupport b → RigidAxi b) := by
  intro h
  have hbad := h false trivial
  simp [RigidAxi] at hbad

/-- Exact countermodel to the inference `support in R∪S` implies support in one
of `R` or `S`. -/
theorem support_in_union_does_not_select_alternative :
    (∀ b, MixedSupport b → Rigid2D b ∨ RigidAxi b) ∧
    ¬ (∀ b, MixedSupport b → Rigid2D b) ∧
    ¬ (∀ b, MixedSupport b → RigidAxi b) := by
  exact ⟨mixed_support_lies_in_rigid_union,
    mixed_support_not_in_2d, mixed_support_not_in_axi⟩

/-- A constant sequence of mixed supports; passing to indices cannot change
its support. -/
def mixedSupportSequence (_n : ℕ) (b : Bool) : Prop := MixedSupport b

theorem every_index_remains_mixed (n : ℕ) :
    (∀ b, mixedSupportSequence n b → Rigid2D b ∨ RigidAxi b) ∧
    ¬ (∀ b, mixedSupportSequence n b → Rigid2D b) ∧
    ¬ (∀ b, mixedSupportSequence n b → RigidAxi b) := by
  simpa [mixedSupportSequence] using support_in_union_does_not_select_alternative

/-- A finite three-configuration coefficient with all configurations maximizing. -/
def finiteCoefficient (_i : Option Bool) : ℚ := 1

/-- The two proposed rigid maximizers omit the third configuration `none`. -/
def ProposedRigid (i : Option Bool) : Prop :=
  i = some false ∨ i = some true

/-- There is a third coefficient-one maximizer outside the proposed rigid set. -/
theorem third_maximizer_outside_proposed_rigid_set :
    finiteCoefficient none = 1 ∧ ¬ ProposedRigid none := by
  simp [finiteCoefficient, ProposedRigid]

/-- Knowing two displayed maximizers does not classify every maximizer. -/
theorem displayed_maximizers_do_not_exhaust_maximizers :
    ¬ (∀ i : Option Bool,
      finiteCoefficient i = 1 → ProposedRigid i) := by
  intro h
  exact third_maximizer_outside_proposed_rigid_set.2
    (h none third_maximizer_outside_proposed_rigid_set.1)

#print axioms mixed_support_lies_in_rigid_union
#print axioms mixed_support_not_in_2d
#print axioms mixed_support_not_in_axi
#print axioms support_in_union_does_not_select_alternative
#print axioms every_index_remains_mixed
#print axioms third_maximizer_outside_proposed_rigid_set
#print axioms displayed_maximizers_do_not_exhaust_maximizers

end Round211NavierStokes
end Millennium
