import Mathlib

/-!
# RH frame floor to Weil negative margin: finite scalar core

This file verifies the exact `2 x 2` scalar inequality behind the statement
that a residual Gram floor transfers linearly to the negative eigenvalue of a
hyperbolic pair operator.

It does not formalize Hilbert-space projections, Schur complements, polar
decomposition, Sylvester inertia, Weil's explicit formula, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHFrameToWeilMarginFinite

/-- A `2 x 2` Hermitian Gram matrix above `F I` has determinant at least `F^2`.
The overlap is written `x + i y`. -/
theorem residual_gram_determinant_ge_floor_sq
    (A C x y F : ℝ)
    (hF : 0 ≤ F)
    (hA : F ≤ A)
    (hC : F ≤ C)
    (hminor : x ^ 2 + y ^ 2 ≤ (A - F) * (C - F)) :
    F ^ 2 ≤ A * C - x ^ 2 - y ^ 2 := by
  have hAF : 0 ≤ A - F := sub_nonneg.mpr hA
  have hCF : 0 ≤ C - F := sub_nonneg.mpr hC
  have hsum : 0 ≤ A + C - 2 * F := by linarith
  nlinarith [mul_nonneg hF hsum, hminor]

/-- Exact complex-overlap formula: if the residual Gram matrix is at least
`F I`, then the magnitude of the negative hyperbolic eigenvalue is at least
`F`, with no determinant-square or upper-norm loss. -/
theorem hyperbolic_negative_margin_ge_floor
    (A C x y F : ℝ)
    (hF : 0 ≤ F)
    (hA : F ≤ A)
    (hC : F ≤ C)
    (hminor : x ^ 2 + y ^ 2 ≤ (A - F) * (C - F)) :
    F ≤ Real.sqrt (A * C - y ^ 2) - x := by
  have hAF : 0 ≤ A - F := sub_nonneg.mpr hA
  have hCF : 0 ≤ C - F := sub_nonneg.mpr hC
  have htwox : 2 * x ≤ (A - F) + (C - F) := by
    by_cases hx : x ≤ 0
    · nlinarith
    · have hxpos : 0 < x := lt_of_not_ge hx
      have hx2 : x ^ 2 ≤ (A - F) * (C - F) := by
        nlinarith [sq_nonneg y]
      have hdiff : 0 ≤ ((A - F) - (C - F)) ^ 2 := sq_nonneg _
      nlinarith
  have hrad : 0 ≤ A * C - y ^ 2 := by
    have hdet := residual_gram_determinant_ge_floor_sq
      A C x y F hF hA hC hminor
    nlinarith [sq_nonneg x, sq_nonneg F]
  have hsq : (x + F) ^ 2 ≤ A * C - y ^ 2 := by
    have hdet := residual_gram_determinant_ge_floor_sq
      A C x y F hF hA hC hminor
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (A * C - y ^ 2) := Real.sqrt_nonneg _
  by_cases hxf : x + F ≤ 0
  · nlinarith
  · have hxfpos : 0 < x + F := lt_of_not_ge hxf
    have hsqrt_sq : (Real.sqrt (A * C - y ^ 2)) ^ 2 = A * C - y ^ 2 := by
      exact Real.sq_sqrt hrad
    nlinarith

/-- If an error of norm at most `eta` is smaller than the linear negative
margin `F`, a strictly negative margin remains. -/
theorem robust_negative_margin
    (F eta : ℝ)
    (heta : eta < F) :
    0 < F - eta := by
  linarith

#print axioms residual_gram_determinant_ge_floor_sq
#print axioms hyperbolic_negative_margin_ge_floor
#print axioms robust_negative_margin

end RHFrameToWeilMarginFinite
end MillenniumBraid
