import Millennium.Hodge.FiniteCore

namespace Millennium.Braid.M4

def Certificate : Prop :=
  ∀ (Y S : Set Bool), Y ⊆ S → S ∩ Y = Y

theorem core : Certificate := by
  intro Y S h
  exact Millennium.Hodge.FiniteCore.contained_intersection h

#print axioms core

end Millennium.Braid.M4
