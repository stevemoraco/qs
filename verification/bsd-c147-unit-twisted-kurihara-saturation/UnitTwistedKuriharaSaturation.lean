import Mathlib

namespace Millennium.BSD.UnitTwistedKuriharaSaturation

theorem unitWitnessPointSaturation
    (R r s : ℕ)
    (hNonzeroIndex : r ≤ s)
    (hUnitWitness : s ≤ R)
    (hPoints : R ≤ r) :
    r = R ∧ s = R := by
  omega

theorem equalEndpointsKillBlockInterval
    (r s blockIndex : ℕ)
    (hEq : r = s)
    (hBlock : r ≤ blockIndex)
    (hStrict : blockIndex < s) :
    False := by
  omega

theorem exactRankKillsDivisibleDefect
    (R mwRank divSha selmerCorank : ℕ)
    (hPoints : R ≤ mwRank)
    (hSelmer : selmerCorank = R)
    (hKummer : selmerCorank = mwRank + divSha) :
    mwRank = R ∧ divSha = 0 := by
  omega

theorem characterwiseZeroSumsToZero
    {ι : Type*}
    (S : Finset ι)
    (defect : ι → ℕ)
    (h : ∀ i ∈ S, defect i = 0) :
    ∑ i ∈ S, defect i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact h i hi

#print axioms unitWitnessPointSaturation
#print axioms equalEndpointsKillBlockInterval
#print axioms exactRankKillsDivisibleDefect
#print axioms characterwiseZeroSumsToZero

end Millennium.BSD.UnitTwistedKuriharaSaturation
