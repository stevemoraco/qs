import Mathlib

namespace B2Round54

def hodgeWitness (i : Fin 6) : Int := if i = 4 then 1 else 0

theorem hodge_projection_core_values :
    And (hodgeWitness 4 = 1) (hodgeWitness 0 = 0) := by
  norm_num [hodgeWitness]

#print axioms hodge_projection_core_values

end B2Round54
