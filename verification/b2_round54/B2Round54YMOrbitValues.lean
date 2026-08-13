import Mathlib

namespace B2Round54

def orbitAct (_ : Unit) (x : Fin 2) : Fin 2 := x

def orbitLabel (x : Fin 2) : Nat := x.val

theorem ym_two_orbit_invariant_values :
    And
      (forall g : Unit, forall x : Fin 2, orbitLabel (orbitAct g x) = orbitLabel x)
      (And (orbitLabel 0 = 0) (orbitLabel 1 = 1)) := by
  constructor
  · intro g x
    rfl
  · norm_num [orbitLabel]

#print axioms ym_two_orbit_invariant_values

end B2Round54
