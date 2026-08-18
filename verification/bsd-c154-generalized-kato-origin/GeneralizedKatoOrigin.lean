import Mathlib

namespace Millennium.BSD.GeneralizedKatoOrigin

theorem geometricKernelClassSaturatesRankTwo
    (mwRank divShaCorank selmerDim : ℕ)
    (hSelmer : selmerDim = 2)
    (hKummer : selmerDim = mwRank + divShaCorank)
    (hGeometricKernel : 2 ≤ mwRank) :
    mwRank = 2 ∧ divShaCorank = 0 := by
  omega

theorem rankTwoKillsDivisibleSha
    (mwRank divShaCorank : ℕ)
    (hExact : 2 = mwRank + divShaCorank)
    (hRank : mwRank = 2) :
    divShaCorank = 0 := by
  omega

theorem zeroDivisibleShaExactifiesRank
    (mwRank divShaCorank : ℕ)
    (hExact : 2 = mwRank + divShaCorank)
    (hSha : divShaCorank = 0) :
    mwRank = 2 := by
  omega

theorem nonGeometricExcludesRankTwo
    (mwRank : ℕ)
    (hRankBound : mwRank ≤ 2)
    (geometric : Prop)
    (hRankTwoGeometric : mwRank = 2 → geometric)
    (hNotGeometric : ¬ geometric) :
    mwRank ≤ 1 := by
  by_contra h
  have hTwo : mwRank = 2 := by omega
  exact hNotGeometric (hRankTwoGeometric hTwo)

#print axioms geometricKernelClassSaturatesRankTwo
#print axioms rankTwoKillsDivisibleSha
#print axioms zeroDivisibleShaExactifiesRank
#print axioms nonGeometricExcludesRankTwo

end Millennium.BSD.GeneralizedKatoOrigin
