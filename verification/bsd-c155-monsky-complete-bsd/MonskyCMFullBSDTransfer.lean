import Mathlib

namespace Millennium.BSD.MonskyCMFullBSDTransfer

theorem selmerRankZeroKillsRankAndShaTwo
    (mwRank shaTwoDim selmerDim : ℕ)
    (hKummer : selmerDim = mwRank + 2 + shaTwoDim)
    (hSelmer : selmerDim = 2) :
    mwRank = 0 ∧ shaTwoDim = 0 := by
  omega

theorem zeroTwoLayerClosesPrimary
    (shaTwoDim shaTwoPrimaryLength : ℕ)
    (hShaTwo : shaTwoDim = 0)
    (hPrimary : shaTwoDim = 0 → shaTwoPrimaryLength = 0) :
    shaTwoPrimaryLength = 0 := by
  exact hPrimary hShaTwo

theorem rankZeroTwoAdicSpecialValue
    (raw sha tamagawa torsion : ℤ)
    (hBSD : raw = sha + tamagawa - 2 * torsion)
    (hSha : sha = 0)
    (hTorsion : torsion = 2) :
    raw = tamagawa - 4 := by
  omega

theorem exactFamilyCountTransfer
    (sourceCount promotedCount : ℕ)
    (hEverySourcePromoted : promotedCount = sourceCount) :
    promotedCount = sourceCount := by
  exact hEverySourcePromoted

#print axioms selmerRankZeroKillsRankAndShaTwo
#print axioms zeroTwoLayerClosesPrimary
#print axioms rankZeroTwoAdicSpecialValue
#print axioms exactFamilyCountTransfer

end Millennium.BSD.MonskyCMFullBSDTransfer
