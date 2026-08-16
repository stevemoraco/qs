import Mathlib

namespace Millennium.BSD.CasselsTateLiftability

theorem radicalDimensionLedger
    (kummerDim liftableShaDim radicalDim : ℕ)
    (h : radicalDim = kummerDim + liftableShaDim) :
    kummerDim ≤ radicalDim := by
  omega

theorem radicalSaturationCertificate
    (pointDim kummerDim liftableShaDim radicalDim : ℕ)
    (hPoints : pointDim ≤ kummerDim)
    (hRadical : radicalDim = kummerDim + liftableShaDim)
    (hSaturated : radicalDim = pointDim) :
    kummerDim = pointDim ∧ liftableShaDim = 0 := by
  omega

theorem liftableExcessLedger
    (divCorank deepPairs liftableShaDim : ℕ)
    (h : liftableShaDim = divCorank + 2 * deepPairs) :
    liftableShaDim % 2 = divCorank % 2 := by
  omega

theorem zeroLiftableExcess
    (divCorank deepPairs liftableShaDim : ℕ)
    (h : liftableShaDim = divCorank + 2 * deepPairs)
    (hZero : liftableShaDim = 0) :
    divCorank = 0 ∧ deepPairs = 0 := by
  omega

theorem originAmbiguityAtOneDepth :
    (2 + 0 = 1 + 1) := by
  norm_num

#print axioms radicalDimensionLedger
#print axioms radicalSaturationCertificate
#print axioms liftableExcessLedger
#print axioms zeroLiftableExcess
#print axioms originAmbiguityAtOneDepth

end Millennium.BSD.CasselsTateLiftability
