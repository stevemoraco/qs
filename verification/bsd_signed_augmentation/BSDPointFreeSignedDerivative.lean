import Mathlib

namespace BSDPointFreeSignedDerivative

/-- Cleared-denominator form of the signed derivative combination entering
Perrin--Riou's logarithm formula when the Frobenius roots are `alpha` and
`-alpha`, with `alpha^2 = -p`. -/
theorem cleared_signed_derivative_identity
    {K : Type*} [CommRing K]
    {p alpha sharp flat lAlpha lBeta : K}
    (hAlpha : alpha ^ 2 * lAlpha = alpha * sharp + flat)
    (hBeta : alpha ^ 2 * lBeta = -alpha * sharp + flat)
    (hSquare : alpha ^ 2 = -p) :
    alpha ^ 2 *
        ((alpha - 1) ^ 2 * lAlpha - (alpha + 1) ^ 2 * lBeta) =
      -2 * alpha * ((p - 1) * sharp + 2 * flat) := by
  calc
    alpha ^ 2 *
        ((alpha - 1) ^ 2 * lAlpha - (alpha + 1) ^ 2 * lBeta) =
      (alpha - 1) ^ 2 * (alpha ^ 2 * lAlpha) -
        (alpha + 1) ^ 2 * (alpha ^ 2 * lBeta) := by ring
    _ = (alpha - 1) ^ 2 * (alpha * sharp + flat) -
        (alpha + 1) ^ 2 * (-alpha * sharp + flat) := by
          rw [hAlpha, hBeta]
    _ = -2 * alpha * ((p - 1) * sharp + 2 * flat) := by
          rw [hSquare]
          ring

/-- In characteristic zero, a nonzero signed derivative combination forces
the cleared Perrin--Riou derivative bracket to be nonzero. -/
theorem cleared_bracket_nonzero_of_signed_combo_nonzero
    {K : Type*} [Field K] [CharZero K]
    {p alpha sharp flat lAlpha lBeta : K}
    (hAlpha : alpha ^ 2 * lAlpha = alpha * sharp + flat)
    (hBeta : alpha ^ 2 * lBeta = -alpha * sharp + flat)
    (hSquare : alpha ^ 2 = -p)
    (hAlphaNonzero : alpha ≠ 0)
    (hCombo : (p - 1) * sharp + 2 * flat ≠ 0) :
    (alpha - 1) ^ 2 * lAlpha - (alpha + 1) ^ 2 * lBeta ≠ 0 := by
  intro hBracket
  have hIdentity := cleared_signed_derivative_identity
    hAlpha hBeta hSquare
  have hZero :
      (-2 : K) * alpha * ((p - 1) * sharp + 2 * flat) = 0 := by
    rw [← hIdentity, hBracket]
    ring
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hAlphaNonzero) hCombo) hZero

/-- Componentwise divisibility of a finite approximation error propagates to
the weighted signed derivative combination. If the finite combination is not
divisible by the modulus, the stable combination is nonzero. -/
theorem weighted_stable_nonzero_of_component_errors
    {modulus p finiteSharp finiteFlat stableSharp stableFlat : ℤ}
    (hSharp : modulus ∣ stableSharp - finiteSharp)
    (hFlat : modulus ∣ stableFlat - finiteFlat)
    (hFinite :
      ¬ modulus ∣ (p - 1) * finiteSharp + 2 * finiteFlat) :
    (p - 1) * stableSharp + 2 * stableFlat ≠ 0 := by
  intro hStable
  apply hFinite
  rcases hSharp with ⟨qSharp, hqSharp⟩
  rcases hFlat with ⟨qFlat, hqFlat⟩
  refine ⟨-((p - 1) * qSharp + 2 * qFlat), ?_⟩
  have hWeighted :
      (p - 1) * (stableSharp - finiteSharp) +
          2 * (stableFlat - finiteFlat) =
        modulus * ((p - 1) * qSharp + 2 * qFlat) := by
    rw [hqSharp, hqFlat]
    ring
  calc
    (p - 1) * finiteSharp + 2 * finiteFlat =
      -((p - 1) * (stableSharp - finiteSharp) +
          2 * (stableFlat - finiteFlat)) := by
        rw [hStable]
        ring
    _ = -(modulus * ((p - 1) * qSharp + 2 * qFlat)) := by
      rw [hWeighted]
    _ = modulus * (-((p - 1) * qSharp + 2 * qFlat)) := by ring

/-- Even-level conversion from signed derivatives to two adjacent raw
Mazur--Tate derivatives. The scalar `sign` records the harmless parity sign. -/
theorem even_raw_signed_combination
    {R : Type*} [CommRing R]
    {p scale sign sharp flat rawNow rawPrevious : R}
    (hSharp : scale * sharp = sign * rawNow)
    (hFlat : scale * flat = -sign * p * rawPrevious) :
    scale * ((p - 1) * sharp + 2 * flat) =
      sign * ((p - 1) * rawNow - 2 * p * rawPrevious) := by
  calc
    scale * ((p - 1) * sharp + 2 * flat) =
      (p - 1) * (scale * sharp) + 2 * (scale * flat) := by ring
    _ = (p - 1) * (sign * rawNow) +
        2 * (-sign * p * rawPrevious) := by rw [hSharp, hFlat]
    _ = sign * ((p - 1) * rawNow - 2 * p * rawPrevious) := by ring

/-- Odd-level conversion from signed derivatives to two adjacent raw
Mazur--Tate derivatives. -/
theorem odd_raw_signed_combination
    {R : Type*} [CommRing R]
    {p scale sign sharp flat rawNow rawPrevious : R}
    (hSharp : scale * sharp = sign * rawPrevious)
    (hFlat : scale * flat = sign * rawNow) :
    scale * ((p - 1) * sharp + 2 * flat) =
      sign * ((p - 1) * rawPrevious + 2 * rawNow) := by
  calc
    scale * ((p - 1) * sharp + 2 * flat) =
      (p - 1) * (scale * sharp) + 2 * (scale * flat) := by ring
    _ = (p - 1) * (sign * rawPrevious) + 2 * (sign * rawNow) := by
      rw [hSharp, hFlat]
    _ = sign * ((p - 1) * rawPrevious + 2 * rawNow) := by ring

/-- Abstract point-free implication chain: finite derivative certificate,
localized Kato nonvanishing, Perrin--Riou, Gross--Zagier--Kolyvagin, and p-BSD. -/
theorem point_free_rank_one_pBSD_chain
    {FiniteCertificate KatoNonzero AnalyticRankOne AlgebraicRankOne
      ShaFinite PrimaryBSD : Prop}
    (hFiniteKato : FiniteCertificate → KatoNonzero)
    (hPerrinRiou : KatoNonzero → AnalyticRankOne)
    (hGZK : AnalyticRankOne → AlgebraicRankOne ∧ ShaFinite)
    (hpBSD : AnalyticRankOne → PrimaryBSD)
    (hCertificate : FiniteCertificate) :
    AnalyticRankOne ∧ AlgebraicRankOne ∧ ShaFinite ∧ PrimaryBSD := by
  have hKato := hFiniteKato hCertificate
  have hAnalytic := hPerrinRiou hKato
  have hArithmetic := hGZK hAnalytic
  exact ⟨hAnalytic, hArithmetic.1, hArithmetic.2, hpBSD hAnalytic⟩

#print axioms cleared_signed_derivative_identity
#print axioms cleared_bracket_nonzero_of_signed_combo_nonzero
#print axioms weighted_stable_nonzero_of_component_errors
#print axioms even_raw_signed_combination
#print axioms odd_raw_signed_combination
#print axioms point_free_rank_one_pBSD_chain

end BSDPointFreeSignedDerivative
