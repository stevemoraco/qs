import Mathlib

namespace Millennium.BSD.KuriharaPointSaturation

theorem pointSaturation
    (r mwRank divShaCorank selmerCorank : ℕ)
    (hKummer : selmerCorank = mwRank + divShaCorank)
    (hPoints : r ≤ mwRank)
    (hKurihara : selmerCorank ≤ r) :
    mwRank = r ∧ selmerCorank = r ∧ divShaCorank = 0 := by
  omega

theorem witnessSupportSaturates
    (r mwRank divShaCorank selmerCorank ordDelta : ℕ)
    (hStructure : selmerCorank = ordDelta)
    (hWitness : ordDelta ≤ r)
    (hKummer : selmerCorank = mwRank + divShaCorank)
    (hPoints : r ≤ mwRank) :
    ordDelta = r ∧ mwRank = r ∧ selmerCorank = r ∧ divShaCorank = 0 := by
  omega

theorem saturationExistsIffNoDivisibleSha
    (mwRank divShaCorank selmerCorank ordDelta : ℕ)
    (hStructure : selmerCorank = ordDelta)
    (hKummer : selmerCorank = mwRank + divShaCorank) :
    (∃ r : ℕ, r ≤ mwRank ∧ ordDelta ≤ r) ↔ divShaCorank = 0 := by
  constructor
  · rintro ⟨r, hPoints, hWitness⟩
    omega
  · intro hZero
    refine ⟨mwRank, le_rfl, ?_⟩
    omega

theorem lowRankAnalyticExactification
    (r mwRank divShaCorank selmerCorank analyticRank : ℕ)
    (hKummer : selmerCorank = mwRank + divShaCorank)
    (hPoints : r ≤ mwRank)
    (hKurihara : selmerCorank ≤ r)
    (hPConverse : analyticRank = selmerCorank) :
    mwRank = r ∧ analyticRank = r ∧ divShaCorank = 0 := by
  omega

#print axioms pointSaturation
#print axioms witnessSupportSaturates
#print axioms saturationExistsIffNoDivisibleSha
#print axioms lowRankAnalyticExactification

end Millennium.BSD.KuriharaPointSaturation
