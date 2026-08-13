import Mathlib

namespace Millennium.NSAOH4BResponse

def gaussianSecondProfile (k c q x : Real) : Real :=
  2 * k * (2 * k * x ^ 2 - 1) * c ^ 2 * q

lemma gaussianSecondProfile_zero (k c q : Real) :
    gaussianSecondProfile k c q 0 = -2 * k * c ^ 2 * q := by
  simp [gaussianSecondProfile]
  ring

#print axioms gaussianSecondProfile_zero

end Millennium.NSAOH4BResponse
