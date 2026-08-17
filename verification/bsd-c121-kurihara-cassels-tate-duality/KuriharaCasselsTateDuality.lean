import Mathlib

namespace Millennium.BSD.KuriharaCasselsTateDuality

theorem dropRecoversExponent
    (qPrev qNow a : ℕ)
    (h : qPrev = qNow + 2 * a) :
    qPrev - qNow = 2 * a := by
  omega

theorem kuriharaDiscreteConvexity
    (qPrev qNow qNext aNow aNext : ℕ)
    (hNow : qPrev = qNow + 2 * aNow)
    (hNext : qNow = qNext + 2 * aNext)
    (hMono : aNext ≤ aNow) :
    2 * qNow ≤ qPrev + qNext := by
  omega

theorem kuriharaPlateauKillsBlock
    (qPrev qNow a : ℕ)
    (hDrop : qPrev = qNow + 2 * a)
    (hPlateau : qPrev = qNow) :
    a = 0 := by
  omega

theorem threeLayerCake
    (c1 c2 c3 d1 d2 d3 : ℕ)
    (h1 : d1 = 2 * (c1 + c2 + c3))
    (h2 : d2 = 2 * (c2 + c3))
    (h3 : d3 = 2 * c3) :
    d1 + d2 + d3 = 2 * c1 + 4 * c2 + 6 * c3 := by
  omega

theorem firstLayerCountsBlocks
    (blocks d1 : ℕ)
    (h : d1 = 2 * blocks) :
    d1 / 2 = blocks := by
  omega

theorem zeroTailKillsDeepBlocks
    (deepPairs d : ℕ)
    (h : d = 2 * deepPairs)
    (hZero : d = 0) :
    deepPairs = 0 := by
  omega

#print axioms dropRecoversExponent
#print axioms kuriharaDiscreteConvexity
#print axioms kuriharaPlateauKillsBlock
#print axioms threeLayerCake
#print axioms firstLayerCountsBlocks
#print axioms zeroTailKillsDeepBlocks

end Millennium.BSD.KuriharaCasselsTateDuality
