import Mathlib

/-!
# Corrected net-Green finite algebra

Finite algebra/sign core for
`CORRECTED_NET_GREEN_UNIFORMITY_AND_THRESHOLD_2026-08-11.md`.

This does NOT prove RH.  The elliptic-integral derivative identities,
Green-function representation, and zeta zero-density passage remain analytic inputs.
-/

namespace RHProof
namespace CorrectedGreenFinite

/-- The numerator decomposition used to compare the two slit factors in the
complex-displacement bound.  This is the division-free form of
`z^2-s = (z^2-s^2)/(1+s) + s*(z^2-1)/(1+s)`. -/
theorem numerator_decomposition_cross (z s : ℂ) :
    (1 + s) * (z ^ 2 - s) =
      (z ^ 2 - s ^ 2) + s * (z ^ 2 - 1) := by
  ring

/-- Pure sign core behind strict decrease of the corrected threshold ratio.
After the elliptic identities are inserted, the derivative of
`F(s)=D(s)-(1-s)A(s)E(s)` is exactly the expression below. -/
theorem corrected_Fprime_positive
    (s A E K : ℝ)
    (hs0 : 0 < s)
    (hs1 : s < 1)
    (hA : 0 < A)
    (hE : 0 < E)
    (hKE : E < K) :
    0 < (A / s) * (s * E + (1 - s) * (K - E)) := by
  have hse : 0 < s * E := mul_pos hs0 hE
  have h1s : 0 < 1 - s := sub_pos.mpr hs1
  have hke : 0 < K - E := sub_pos.mpr hKE
  have htail : 0 < (1 - s) * (K - E) := mul_pos h1s hke
  have hsum : 0 < s * E + (1 - s) * (K - E) := add_pos hse htail
  have hAs : 0 < A / s := div_pos hA hs0
  exact mul_pos hAs hsum

/-- If the corrected auxiliary quantity
`F = D-(1-s)AE` is positive, then the numerator governing the derivative of
`H=D/A` is strictly negative. -/
theorem corrected_ratio_numerator_negative
    (s A D E : ℝ)
    (hF : 0 < D - (1 - s) * A * E) :
    (1 - s) * A * E - D < 0 := by
  linarith

/-- A convenient positivity form for the denominator of the corrected ratio
when `0<s<1` and `A>0`. -/
theorem corrected_ratio_denominator_positive
    (s A : ℝ)
    (hs0 : 0 < s)
    (hs1 : s < 1)
    (hA : 0 < A) :
    0 < (1 - s ^ 2) * A ^ 2 := by
  have hsm1 : -1 < s := lt_trans (by norm_num) hs0
  have hsabs : |s| < 1 := (abs_lt).2 ⟨hsm1, hs1⟩
  have hsquare : s ^ 2 < 1 := (sq_lt_one_iff).2 hsabs
  have h1 : 0 < 1 - s ^ 2 := sub_pos.mpr hsquare
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  exact mul_pos h1 hA2

end CorrectedGreenFinite
end RHProof
