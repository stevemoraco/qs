import Mathlib

namespace Millennium.BSD.GrossRowAnalyticRankZeroCertificate

theorem separatingFamilyFindsWitness
    {C J : Type*} [Zero C]
    (detect : C → J → ZMod 2)
    (hSeparates : ∀ c : C, (∀ j, detect c j = 0) → c = 0)
    (c : C) (hc : c ≠ 0) :
    ∃ j : J, detect c j ≠ 0 := by
  by_contra h
  push_neg at h
  exact hc (hSeparates c h)

theorem oddIntegerPairingNonzero
    (pairing : ℤ)
    (hOdd : pairing % 2 = 1) :
    pairing ≠ 0 := by
  omega

theorem nonzeroSquareProductForcesTwoFactors
    (pairing scalar L1 L2 : ℝ)
    (hFormula : pairing * pairing = scalar * L1 * L2)
    (hPairing : pairing ≠ 0) :
    L1 ≠ 0 ∧ L2 ≠ 0 := by
  constructor
  · intro hL1
    have hsq : pairing * pairing = 0 := by
      simpa [hL1] using hFormula
    rcases mul_eq_zero.mp hsq with h | h
    · exact hPairing h
    · exact hPairing h
  · intro hL2
    have hsq : pairing * pairing = 0 := by
      simpa [hL2] using hFormula
    rcases mul_eq_zero.mp hsq with h | h
    · exact hPairing h
    · exact hPairing h

theorem nonzeroSquareProductForcesScalar
    (pairing scalar L1 L2 : ℝ)
    (hFormula : pairing * pairing = scalar * L1 * L2)
    (hPairing : pairing ≠ 0) :
    scalar ≠ 0 := by
  intro hScalar
  have hsq : pairing * pairing = 0 := by
    simpa [hScalar] using hFormula
  rcases mul_eq_zero.mp hsq with h | h
  · exact hPairing h
  · exact hPairing h

#print axioms separatingFamilyFindsWitness
#print axioms oddIntegerPairingNonzero
#print axioms nonzeroSquareProductForcesTwoFactors
#print axioms nonzeroSquareProductForcesScalar

end Millennium.BSD.GrossRowAnalyticRankZeroCertificate
