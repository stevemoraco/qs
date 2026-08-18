import Mathlib

namespace Millennium.BSD.MazurTateDerivativeSaturation

theorem parityCorrectedBudget
    (q rp splitCount correction : ℕ)
    (hLower : rp + splitCount + 2 * correction ≤ q)
    (hParity : q % 2 = rp % 2) :
    rp + splitCount + 2 * correction + splitCount % 2 ≤ q := by
  omega

theorem derivativeSaturation
    (q rp mwRank divSha pointRank splitCount correction upper : ℕ)
    (hLower : rp + splitCount + 2 * correction ≤ q)
    (hParity : q % 2 = rp % 2)
    (hKummer : rp = mwRank + divSha)
    (hPoints : pointRank ≤ mwRank)
    (hObserved : q ≤ upper)
    (hBudget :
      upper ≤ pointRank + splitCount + 2 * correction + splitCount % 2) :
    q = pointRank + splitCount + 2 * correction + splitCount % 2 ∧
      rp = pointRank ∧ mwRank = pointRank ∧ divSha = 0 := by
  have hSharp := parityCorrectedBudget q rp splitCount correction hLower hParity
  omega

theorem rankZeroDerivativeCertificate
    (q rp mwRank divSha splitCount correction upper : ℕ)
    (hLower : rp + splitCount + 2 * correction ≤ q)
    (hParity : q % 2 = rp % 2)
    (hKummer : rp = mwRank + divSha)
    (hObserved : q ≤ upper)
    (hBudget :
      upper ≤ splitCount + 2 * correction + splitCount % 2) :
    rp = 0 ∧ mwRank = 0 ∧ divSha = 0 := by
  have h := derivativeSaturation
    q rp mwRank divSha 0 splitCount correction upper
    hLower hParity hKummer (Nat.zero_le mwRank) hObserved hBudget
  omega

#print axioms parityCorrectedBudget
#print axioms derivativeSaturation
#print axioms rankZeroDerivativeCertificate

end Millennium.BSD.MazurTateDerivativeSaturation
