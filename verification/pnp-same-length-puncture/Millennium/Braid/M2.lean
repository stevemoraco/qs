import Millennium.PNP.GraphWalkConstraintFirewall

namespace Millennium.Braid.M2

def Certificate : Prop :=
  (∀ i : Fin 2,
    ∃ w : Millennium.PNP.GraphWalkConstraint.ChoiceWalk 2,
      Millennium.PNP.GraphWalkConstraint.correlated2 w ∧
      w i = Millennium.PNP.GraphWalkConstraint.mixed2 i) ∧
  ¬ Millennium.PNP.GraphWalkConstraint.correlated2
      Millennium.PNP.GraphWalkConstraint.mixed2

theorem core : Certificate :=
  Millennium.PNP.GraphWalkConstraint.all_local_extensions_do_not_force_global

#print axioms core

end Millennium.Braid.M2
