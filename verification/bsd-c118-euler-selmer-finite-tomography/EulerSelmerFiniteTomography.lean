import Mathlib

namespace Millennium.BSD.EulerSelmerFiniteTomography

theorem pairedBlockCountFromPtorsion
    (e r s : ℕ)
    (h : s = e + 2 * r) :
    (s - e) / 2 = r := by
  omega

theorem largestExponentFromFirstDrop
    (delta0 delta1 d0 : ℕ)
    (h : delta0 = d0 + delta1) :
    d0 = delta0 - delta1 := by
  omega

theorem threeBlockOrderFromBoundary
    (delta0 delta1 delta2 delta3 d0 d1 d2 : ℕ)
    (h0 : delta0 = d0 + delta1)
    (h1 : delta1 = d1 + delta2)
    (h2 : delta2 = d2 + delta3) :
    2 * (d0 + d1 + d2) = 2 * (delta0 - delta3) := by
  omega

theorem plateauStopsLaterSpectrum
    (delta nextDelta d later : ℕ)
    (hDrop : delta = d + nextDelta)
    (hPlateau : delta = nextDelta)
    (hLater : later ≤ d) :
    d = 0 ∧ later = 0 := by
  omega

theorem rankOnePairedBlockCount
    (r s : ℕ)
    (h : s = 1 + 2 * r) :
    (s - 1) / 2 = r := by
  omega

#print axioms pairedBlockCountFromPtorsion
#print axioms largestExponentFromFirstDrop
#print axioms threeBlockOrderFromBoundary
#print axioms plateauStopsLaterSpectrum
#print axioms rankOnePairedBlockCount

end Millennium.BSD.EulerSelmerFiniteTomography
