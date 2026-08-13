import Mathlib

namespace GrandSquare

theorem identity (A B : ℚ) :
    A ^ 2 - B ^ 2 = (A - B) * (A + B) := by
  ring

#print axioms identity

end GrandSquare
