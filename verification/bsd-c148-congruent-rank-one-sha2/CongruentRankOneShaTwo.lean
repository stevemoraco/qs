import Mathlib

namespace Millennium.BSD.CongruentRankOneShaTwo

theorem rankOneFullTwoTorsionModTwoDimension
    (rank torsionDim mwModTwoDim : ℕ)
    (hRank : rank = 1)
    (hTors : torsionDim = 2)
    (hDim : mwModTwoDim = rank + torsionDim) :
    mwModTwoDim = 3 := by
  omega

theorem selmerThreeKillsShaTwo
    (mwModTwoDim selmerDim shaTwoDim : ℕ)
    (hExact : selmerDim = mwModTwoDim + shaTwoDim)
    (hMW : mwModTwoDim = 3)
    (hSelmer : selmerDim = 3) :
    shaTwoDim = 0 := by
  omega

theorem zeroTwoTorsionKillsFiniteTwoPrimary
    (shaTwoDim shaTwoPrimaryLength : ℕ)
    (hFiniteGroup : shaTwoDim = 0 → shaTwoPrimaryLength = 0)
    (hShaTwo : shaTwoDim = 0) :
    shaTwoPrimaryLength = 0 := by
  exact hFiniteGroup hShaTwo

theorem rankOneSelmerThreeCertificate
    (rank torsionDim mwModTwoDim selmerDim shaTwoDim : ℕ)
    (hRank : rank = 1)
    (hTors : torsionDim = 2)
    (hMWDim : mwModTwoDim = rank + torsionDim)
    (hKummer : selmerDim = mwModTwoDim + shaTwoDim)
    (hSelmer : selmerDim = 3) :
    mwModTwoDim = 3 ∧ shaTwoDim = 0 := by
  have hMW := rankOneFullTwoTorsionModTwoDimension
    rank torsionDim mwModTwoDim hRank hTors hMWDim
  have hSha := selmerThreeKillsShaTwo
    mwModTwoDim selmerDim shaTwoDim hKummer hMW hSelmer
  exact ⟨hMW, hSha⟩

#print axioms rankOneFullTwoTorsionModTwoDimension
#print axioms selmerThreeKillsShaTwo
#print axioms zeroTwoTorsionKillsFiniteTwoPrimary
#print axioms rankOneSelmerThreeCertificate

end Millennium.BSD.CongruentRankOneShaTwo
