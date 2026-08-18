import Mathlib

namespace Millennium.BSD.CMExactDelaunayFullBSDDensity

theorem rankTwoElementaryWeightRatio :
    (4 : ℚ) / 6 = 2 / 3 := by
  norm_num

theorem elementaryStratumCoefficient
    (c d : ℚ)
    (h : d = ((4 : ℚ) / 6) * c) :
    d = (2 / 3) * c := by
  rw [rankTwoElementaryWeightRatio] at h
  exact h

theorem exactStratumTransfer
    (stratumCount bsdCount : ℕ)
    (h : bsdCount = stratumCount) :
    bsdCount = stratumCount := h

theorem subgroupContainsGeneratedSum
    {A : Type*} [AddGroup A]
    (H : AddSubgroup A) (x y : A)
    (hx : x ∈ H) (hy : y ∈ H) :
    x + y ∈ H := by
  exact H.add_mem hx hy

#print axioms rankTwoElementaryWeightRatio
#print axioms elementaryStratumCoefficient
#print axioms exactStratumTransfer
#print axioms subgroupContainsGeneratedSum

end Millennium.BSD.CMExactDelaunayFullBSDDensity
