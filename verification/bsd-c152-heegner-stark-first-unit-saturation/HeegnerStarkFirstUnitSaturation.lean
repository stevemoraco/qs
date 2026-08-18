import Mathlib

namespace Millennium.BSD.HeegnerStarkFirstUnitSaturation

theorem equivariantLengthSaturation
    (r ringLength kummerLength selmerLength shaLength : ℕ)
    (hKummerFree : kummerLength = r * ringLength)
    (hInject : kummerLength ≤ selmerLength)
    (hGenerated : selmerLength ≤ r * ringLength)
    (hExact : selmerLength = kummerLength + shaLength) :
    selmerLength = kummerLength ∧ shaLength = 0 := by
  omega

theorem basePointFittingSaturation
    (r pointDim selmerDim shaDim : ℕ)
    (hPoints : r ≤ pointDim)
    (hFitting : selmerDim ≤ r)
    (hKummer : selmerDim = pointDim + shaDim) :
    pointDim = r ∧ selmerDim = r ∧ shaDim = 0 := by
  omega

theorem firstLayerClosesPrimary
    (shaPDim shaPrimaryLength : ℕ)
    (hShaP : shaPDim = 0)
    (hPrimary :
      shaPDim = 0 → shaPrimaryLength = 0) :
    shaPrimaryLength = 0 := by
  exact hPrimary hShaP

theorem thresholdAtOrBelowKummerRank
    (threshold kummerRank : ℕ)
    (hThreshold : threshold ≤ kummerRank)
    (hLower : kummerRank ≤ threshold) :
    threshold = kummerRank := by
  omega

#print axioms equivariantLengthSaturation
#print axioms basePointFittingSaturation
#print axioms firstLayerClosesPrimary
#print axioms thresholdAtOrBelowKummerRank

end Millennium.BSD.HeegnerStarkFirstUnitSaturation
