import Mathlib

namespace Millennium.BSD.GeneralizedKatoGap

theorem katoNonzeroIffSelmerTwo
    (selmerDim : ℕ)
    (KatoNonzero : Prop)
    (hForward : KatoNonzero → selmerDim = 2)
    (hBackward : selmerDim = 2 → KatoNonzero) :
    KatoNonzero ↔ selmerDim = 2 := by
  exact ⟨hForward, hBackward⟩

theorem zeroKatoForcesSelmerAtLeastFour
    (selmerDim : ℕ)
    (KatoNonzero : Prop)
    (hPositive : 1 ≤ selmerDim)
    (hEven : selmerDim % 2 = 0)
    (hTwoImpliesKato : selmerDim = 2 → KatoNonzero)
    (hZero : ¬ KatoNonzero) :
    4 ≤ selmerDim := by
  have hNotTwo : selmerDim ≠ 2 := by
    intro hTwo
    exact hZero (hTwoImpliesKato hTwo)
  omega

theorem zeroKatoContradictsRankTwoBsdPrediction
    (selmerDim analyticRank : ℕ)
    (KatoNonzero : Prop)
    (hAnalytic : analyticRank = 2)
    (hPositive : 1 ≤ selmerDim)
    (hEven : selmerDim % 2 = 0)
    (hTwoImpliesKato : selmerDim = 2 → KatoNonzero)
    (hZero : ¬ KatoNonzero)
    (hBsdPrediction : selmerDim = analyticRank) :
    False := by
  have hFour := zeroKatoForcesSelmerAtLeastFour
    selmerDim KatoNonzero hPositive hEven hTwoImpliesKato hZero
  omega

theorem zeroBranchKummerDefect
    (selmerDim mwRank divSha : ℕ)
    (hFour : 4 ≤ selmerDim)
    (hKummer : selmerDim = mwRank + divSha) :
    4 ≤ mwRank + divSha := by
  omega

theorem rankTwoOnZeroBranchForcesShaCorankTwo
    (selmerDim mwRank divSha : ℕ)
    (hFour : 4 ≤ selmerDim)
    (hKummer : selmerDim = mwRank + divSha)
    (hRank : mwRank = 2) :
    2 ≤ divSha := by
  omega

#print axioms katoNonzeroIffSelmerTwo
#print axioms zeroKatoForcesSelmerAtLeastFour
#print axioms zeroKatoContradictsRankTwoBsdPrediction
#print axioms zeroBranchKummerDefect
#print axioms rankTwoOnZeroBranchForcesShaCorankTwo

end Millennium.BSD.GeneralizedKatoGap
