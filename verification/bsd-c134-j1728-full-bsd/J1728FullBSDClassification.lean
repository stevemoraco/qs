import Mathlib

namespace Millennium.BSD.J1728FullBSDClassification

theorem zero_rank_zero_divSha_forces_zero_selmer
    (mwRank divShaCorank selmerCorank : ℕ)
    (hKummer : selmerCorank = mwRank + divShaCorank)
    (hRank : mwRank = 0)
    (hDivSha : divShaCorank = 0) :
    selmerCorank = 0 := by
  omega

theorem pConverse_then_cmBSD
    (selmerZero analyticZero fullBSD : Prop)
    (hSelmer : selmerZero)
    (hPConverse : selmerZero → analyticZero)
    (hCMBSD : analyticZero → fullBSD) :
    fullBSD := by
  exact hCMBSD (hPConverse hSelmer)

theorem residue_five_mod_eight (q : ℕ)
    (h : q % 56 = 5 ∨ q % 56 = 13 ∨ q % 56 = 45) :
    q % 8 = 5 := by
  rcases h with h | h | h <;> omega

theorem residue_nonresidue_classes_mod_seven (q : ℕ)
    (h : q % 56 = 5 ∨ q % 56 = 13 ∨ q % 56 = 45) :
    q % 7 = 5 ∨ q % 7 = 6 ∨ q % 7 = 3 := by
  rcases h with h | h | h
  · left; omega
  · right; left; omega
  · right; right; omega

theorem three_of_twenty_four_is_one_eighth :
    (3 : ℚ) / 24 = 1 / 8 := by
  norm_num

#print axioms zero_rank_zero_divSha_forces_zero_selmer
#print axioms pConverse_then_cmBSD
#print axioms residue_five_mod_eight
#print axioms residue_nonresidue_classes_mod_seven
#print axioms three_of_twenty_four_is_one_eighth

end Millennium.BSD.J1728FullBSDClassification
