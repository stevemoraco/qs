import Mathlib

namespace Millennium.PNP.PedigreeAxiomAudit

structure AdvertisedPredicates where
  QuickProtocol : Type → Prop
  Separation : Type → Prop
  Optimisation : Type → Prop
  STSPinP : Prop
  SATinP : Prop
  PequalsNP : Prop

structure AbstractAxiomChain (A : AdvertisedPredicates) where
  SourceObject : Type
  ProjectedObject : Type
  quick : A.QuickProtocol SourceObject
  project : A.QuickProtocol SourceObject → A.QuickProtocol ProjectedObject
  separate : A.QuickProtocol ProjectedObject → A.Separation ProjectedObject
  optimise : A.Separation ProjectedObject → A.Optimisation ProjectedObject
  solvesSTSP : A.Optimisation ProjectedObject → A.STSPinP
  reducesToSAT : A.STSPinP → A.SATinP
  closes : A.SATinP → A.PequalsNP

theorem conclusion_of_abstract_axiom_chain
    {A : AdvertisedPredicates} (C : AbstractAxiomChain A) :
    A.PequalsNP := by
  exact C.closes (C.reducesToSAT (C.solvesSTSP
    (C.optimise (C.separate (C.project C.quick)))))

def falseAdvertisedPredicates : AdvertisedPredicates where
  QuickProtocol := fun _ => False
  Separation := fun _ => False
  Optimisation := fun _ => False
  STSPinP := False
  SATinP := False
  PequalsNP := False

theorem false_goal_has_no_abstract_chain :
    ¬ Nonempty (AbstractAxiomChain falseAdvertisedPredicates) := by
  rintro ⟨C⟩
  exact conclusion_of_abstract_axiom_chain C

abbrev ProjectedPlaceholder := Unit

theorem projectedPlaceholder_card :
    Fintype.card ProjectedPlaceholder = 1 := by
  simp [ProjectedPlaceholder]

theorem no_bool_embedding_projectedPlaceholder :
    ¬ ∃ f : Bool → ProjectedPlaceholder, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hsame : f false = f true := Subsingleton.elim _ _
  have hfalse : (false : Bool) = true := hf hsame
  exact Bool.false_ne_true hfalse

theorem opaque_protocol_has_no_algorithmic_content
    (QuickProtocol : Type → Prop) (P : Type)
    (h : QuickProtocol P) : QuickProtocol P := by
  exact h

#print axioms conclusion_of_abstract_axiom_chain
#print axioms false_goal_has_no_abstract_chain
#print axioms projectedPlaceholder_card
#print axioms no_bool_embedding_projectedPlaceholder
#print axioms opaque_protocol_has_no_algorithmic_content

end Millennium.PNP.PedigreeAxiomAudit
