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

theorem adjacentLiftabilityDrop
    (divCorank exactBlocks deeperTail dNow dNext : ℕ)
    (hNow : dNow = divCorank + 2 * (exactBlocks + deeperTail))
    (hNext : dNext = divCorank + 2 * deeperTail) :
    dNow = dNext + 2 * exactBlocks := by
  omega

theorem zeroTailStopsAllDeeperData
    (divCorank survivingPairs dM : ℕ)
    (h : dM = divCorank + 2 * survivingPairs)
    (hZero : dM = 0) :
    divCorank = 0 ∧ survivingPairs = 0 := by
  omega

theorem threeLayerCake
    (d1 d2 d3 c1 c2 c3 : ℕ)
    (h1 : d1 = 2 * (c1 + c2 + c3))
    (h2 : d2 = 2 * (c2 + c3))
    (h3 : d3 = 2 * c3) :
    d1 + d2 + d3 = 2 * c1 + 4 * c2 + 6 * c3 := by
  omega

theorem originAmbiguityAtOneDepth :
    (2 + 0 = 1 + 1) := by
  norm_num

#print axioms radicalDimensionLedger
#print axioms radicalSaturationCertificate
#print axioms liftableExcessLedger
#print axioms zeroLiftableExcess
#print axioms adjacentLiftabilityDrop
#print axioms zeroTailStopsAllDeeperData
#print axioms threeLayerCake
#print axioms originAmbiguityAtOneDepth

end Millennium.BSD.CasselsTateLiftability
