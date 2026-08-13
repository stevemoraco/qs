import Mathlib

namespace BSD.SelmerCorankSpectralSqueeze

/-- If `s = r + t` and `r ≤ L`, then the excess exact Selmer corank above the
rank budget is a lower bound for the Tate--Shafarevich corank. -/
theorem shaCorank_lowerBound_of_rankUpper
    {s r t L : ℕ}
    (hSelmer : s = r + t)
    (hRankUpper : r ≤ L) :
    s - L ≤ t := by
  omega

/-- A strict Selmer-corank/rank-budget gap forces positive Sha corank. -/
theorem positiveShaCorank_of_selmerAboveRankBudget
    {s r t L : ℕ}
    (hSelmer : s = r + t)
    (hRankUpper : r ≤ L)
    (hGap : L < s) :
    0 < t := by
  omega

/-- Independent lower and upper bounds on rank trap Sha corank in an explicit interval. -/
theorem shaCorank_interval
    {R s r t L : ℕ}
    (hSelmer : s = r + t)
    (hRankLower : R ≤ r)
    (hRankUpper : r ≤ L) :
    s - L ≤ t ∧ t ≤ s - R := by
  omega

/-- Triple saturation closes the corank ledger. -/
theorem tripleSaturation_closesShaCorank
    {R s r t L : ℕ}
    (hSelmer : s = r + t)
    (hRankLower : R ≤ r)
    (hRankUpper : r ≤ L)
    (hRL : R = L)
    (hLs : L = s) :
    r = s ∧ t = 0 := by
  omega

/-- Saturating exact Selmer corank by independent rational points already forces zero Sha corank. -/
theorem descentSaturatesSelmer_closesShaCorank
    {R s r t : ℕ}
    (hSelmer : s = r + t)
    (hRankLower : R ≤ r)
    (hRs : R = s) :
    r = s ∧ t = 0 := by
  omega

/-- Any certified portion `d` of the Selmer-minus-rank-budget gap is a certified Sha-corank lower bound. -/
theorem spectralSelmerGap_certificate
    {s r t L d : ℕ}
    (hSelmer : s = r + t)
    (hRankUpper : r ≤ L)
    (hGap : d ≤ s - L) :
    d ≤ t := by
  exact hGap.trans (shaCorank_lowerBound_of_rankUpper hSelmer hRankUpper)

#print axioms shaCorank_lowerBound_of_rankUpper
#print axioms positiveShaCorank_of_selmerAboveRankBudget
#print axioms shaCorank_interval
#print axioms tripleSaturation_closesShaCorank
#print axioms descentSaturatesSelmer_closesShaCorank
#print axioms spectralSelmerGap_certificate

end BSD.SelmerCorankSpectralSqueeze
