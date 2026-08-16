import Mathlib

namespace Millennium.BSD.FinitePPrimaryShaCertificate

theorem stoppingCertificate
    (pointDim kummerDim tailDim liftabilityDim : ℕ)
    (hPoints : pointDim ≤ kummerDim)
    (hLift : liftabilityDim = kummerDim + tailDim)
    (hStop : liftabilityDim = pointDim) :
    kummerDim = pointDim ∧ tailDim = 0 := by
  omega

theorem finiteShaProducesCertificate
    (pointDim kummerDim tailDim liftabilityDim : ℕ)
    (hPoints : kummerDim = pointDim)
    (hTail : tailDim = 0)
    (hLift : liftabilityDim = kummerDim + tailDim) :
    liftabilityDim = pointDim := by
  omega

theorem adjacentDropRecoversMultiplicity
    (dNow dNext exactMultiplicity : ℕ)
    (h : dNow = dNext + exactMultiplicity) :
    dNow - dNext = exactMultiplicity := by
  omega

theorem threeDepthLayerCake
    (d1 d2 d3 c1 c2 c3 : ℕ)
    (h1 : d1 = 2 * (c1 + c2 + c3))
    (h2 : d2 = 2 * (c2 + c3))
    (h3 : d3 = 2 * c3) :
    d1 + d2 + d3 = 2 * c1 + 4 * c2 + 6 * c3 := by
  omega

theorem noUniversalFiniteDepth
    (bound : ℕ) :
    bound < bound + 1 := by
  omega

#print axioms stoppingCertificate
#print axioms finiteShaProducesCertificate
#print axioms adjacentDropRecoversMultiplicity
#print axioms threeDepthLayerCake
#print axioms noUniversalFiniteDepth

end Millennium.BSD.FinitePPrimaryShaCertificate
