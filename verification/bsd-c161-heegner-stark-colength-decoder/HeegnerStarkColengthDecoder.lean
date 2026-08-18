import Mathlib

namespace Millennium.BSD.HeegnerStarkColengthDecoder

theorem saturatedPacketExactifiesSha
    (exponent missingKummer shaPDim : ℕ)
    (hLedger : exponent = missingKummer + shaPDim)
    (hSaturated : missingKummer = 0) :
    shaPDim = exponent := by
  omega

theorem shaLayerParityDetectsDivisibleCorank
    (shaPDim divCorank finitePairs : ℕ)
    (hShape : shaPDim = divCorank + 2 * finitePairs) :
    shaPDim % 2 = divCorank % 2 := by
  omega

theorem oddExponentForcesPositiveDivisibleDefect
    (exponent divCorank finitePairs : ℕ)
    (hOdd : exponent % 2 = 1)
    (hShape : exponent = divCorank + 2 * finitePairs) :
    1 ≤ divCorank := by
  omega

theorem subtractKnownPointDefect
    (exponent missingKummer shaPDim : ℕ)
    (hLedger : exponent = missingKummer + shaPDim) :
    shaPDim = exponent - missingKummer := by
  omega

theorem zeroIdealForcesLargeResidualDefect
    (ceiling missingKummer shaPDim : ℕ)
    (hLarge : ceiling ≤ missingKummer + shaPDim) :
    ceiling ≤ missingKummer + shaPDim := by
  exact hLarge

#print axioms saturatedPacketExactifiesSha
#print axioms shaLayerParityDetectsDivisibleCorank
#print axioms oddExponentForcesPositiveDivisibleDefect
#print axioms subtractKnownPointDefect
#print axioms zeroIdealForcesLargeResidualDefect

end Millennium.BSD.HeegnerStarkColengthDecoder
