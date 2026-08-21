import Mathlib

/-!
# K3-generated motive retract transfer

This file formalizes the exact range-transfer step used after a Hodge class on a
motive is embedded into an ambient finite product of K3 motives.

If the motive is an algebraic direct summand, there are class-level inclusion
and projection maps and a cycle-level projector. Naturality of the cycle-class
map and the retraction identity imply that an algebraic representative on the
ambient object projects to an algebraic representative on the summand.

No Chow motive, K3 surface, algebraic correspondence, Hodge structure, or Hodge
conjecture is defined here. Those geometric objects are represented by explicit
maps and their exact compatibility laws.
-/

namespace Millennium.Hodge.K3GeneratedMotiveRetractTransfer

variable {CycleAmbient CycleSummand HAmbient HSummand : Type*}

/-- A class lies in the image of a chosen cycle-class map. -/
def Algebraic {Cycle H : Type*} (classMap : Cycle → H) (α : H) : Prop :=
  α ∈ Set.range classMap

/--
The exact data of an algebraic retract from an ambient cycle theory to a
summand cycle theory.
-/
structure AlgebraicRetractData where
  classAmbient : CycleAmbient → HAmbient
  classSummand : CycleSummand → HSummand
  includeClass : HSummand → HAmbient
  projectClass : HAmbient → HSummand
  projectCycle : CycleAmbient → CycleSummand
  class_naturality :
    ∀ z, projectClass (classAmbient z) = classSummand (projectCycle z)
  leftInverse : Function.LeftInverse projectClass includeClass

/--
An algebraic representative of the included summand class projects to an
algebraic representative on the summand.
-/
theorem algebraic_of_included_algebraic
    (D : AlgebraicRetractData
      (CycleAmbient := CycleAmbient) (CycleSummand := CycleSummand)
      (HAmbient := HAmbient) (HSummand := HSummand))
    (α : HSummand)
    (hα : Algebraic D.classAmbient (D.includeClass α)) :
    Algebraic D.classSummand α := by
  rcases hα with ⟨z, hz⟩
  refine ⟨D.projectCycle z, ?_⟩
  calc
    D.classSummand (D.projectCycle z) =
        D.projectClass (D.classAmbient z) :=
      (D.class_naturality z).symm
    _ = D.projectClass (D.includeClass α) := by rw [hz]
    _ = α := D.leftInverse α

/--
If every included summand class is algebraic on the ambient object, then every
summand class is algebraic.
-/
theorem all_summand_classes_of_all_included_classes
    (D : AlgebraicRetractData
      (CycleAmbient := CycleAmbient) (CycleSummand := CycleSummand)
      (HAmbient := HAmbient) (HSummand := HSummand))
    (hall : ∀ α : HSummand, Algebraic D.classAmbient (D.includeClass α)) :
    ∀ α : HSummand, Algebraic D.classSummand α := by
  intro α
  exact algebraic_of_included_algebraic D α (hall α)

/--
Predicate-restricted version for the Hodge classes in one selected degree and
codimension.
-/
theorem all_predicate_summand_classes
    (D : AlgebraicRetractData
      (CycleAmbient := CycleAmbient) (CycleSummand := CycleSummand)
      (HAmbient := HAmbient) (HSummand := HSummand))
    (PS : HSummand → Prop) (PA : HAmbient → Prop)
    (hinclude : ∀ α, PS α → PA (D.includeClass α))
    (hambient : ∀ β, PA β → Algebraic D.classAmbient β) :
    ∀ α, PS α → Algebraic D.classSummand α := by
  intro α hα
  exact algebraic_of_included_algebraic D α
    (hambient (D.includeClass α) (hinclude α hα))

/--
A projector form of the same theorem: an algebraic class fixed by an algebraic
projector has a projected algebraic representative.
-/
theorem algebraic_of_projector_fixed
    {Cycle H : Type*}
    (classMap : Cycle → H)
    (projectClass : H → H)
    (projectCycle : Cycle → Cycle)
    (hnat : ∀ z, projectClass (classMap z) = classMap (projectCycle z))
    (α : H)
    (hfixed : projectClass α = α)
    (halg : Algebraic classMap α) :
    Algebraic classMap α := by
  rcases halg with ⟨z, hz⟩
  refine ⟨projectCycle z, ?_⟩
  calc
    classMap (projectCycle z) = projectClass (classMap z) := (hnat z).symm
    _ = projectClass α := by rw [hz]
    _ = α := hfixed

#print axioms algebraic_of_included_algebraic
#print axioms all_summand_classes_of_all_included_classes
#print axioms all_predicate_summand_classes
#print axioms algebraic_of_projector_fixed

end Millennium.Hodge.K3GeneratedMotiveRetractTransfer
