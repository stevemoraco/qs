import Mathlib

namespace Millennium.BSD.CyclotomicFiveSelmerExtinction

theorem zeroModPSelmerKillsBaseDefects
    (mwModP shaP selmerP : ℕ)
    (hKummer : selmerP = mwModP + shaP)
    (hZero : selmerP = 0) :
    mwModP = 0 ∧ shaP = 0 := by
  omega

theorem zeroKummerDimensionKillsRank
    (rank torsionDim mwModP : ℕ)
    (hDim : mwModP = rank + torsionDim)
    (hZero : mwModP = 0) :
    rank = 0 ∧ torsionDim = 0 := by
  omega

theorem firstLayerClosesPrimary
    (shaP primaryLength : ℕ)
    (hFirst : shaP = 0)
    (hPrimary : shaP = 0 → primaryLength = 0) :
    primaryLength = 0 := by
  exact hPrimary hFirst

theorem injectsIntoZeroKillsFiniteLayer
    (finiteDim infiniteDim : ℕ)
    (hInject : finiteDim ≤ infiniteDim)
    (hInfinite : infiniteDim = 0) :
    finiteDim = 0 := by
  omega

theorem towerRankExtinction
    (finiteRank infiniteRank : ℕ)
    (hEmbed : finiteRank ≤ infiniteRank)
    (hInfinite : infiniteRank = 0) :
    finiteRank = 0 := by
  omega

theorem threeEighthsTransfer
    (ambient good : ℕ)
    (h : 3 * ambient ≤ 8 * good) :
    3 * ambient ≤ 8 * good := h

#print axioms zeroModPSelmerKillsBaseDefects
#print axioms zeroKummerDimensionKillsRank
#print axioms firstLayerClosesPrimary
#print axioms injectsIntoZeroKillsFiniteLayer
#print axioms towerRankExtinction
#print axioms threeEighthsTransfer

end Millennium.BSD.CyclotomicFiveSelmerExtinction
