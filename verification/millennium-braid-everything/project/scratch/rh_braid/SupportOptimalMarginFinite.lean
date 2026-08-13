import Mathlib

/-!
# Finite scalar core for the support-optimal reflected-pair margin

This file contains only the elementary algebra used in
`OPTIMAL_SUPPORT_PSD_DISTANCE_2026-08-11.md`.
It does not formalize the Hilbert-space compression theorem and does not prove RH.
-/

namespace RHProof
namespace SupportOptimalMarginFinite

/-- If `m > 0` and `0 ≤ C < N`, the two candidate eigenvalues
`m(C-N)` and `m(C+N)` have opposite signs. -/
theorem eigenvalue_signs
    (m N C : ℝ)
    (hm : 0 < m)
    (hC : 0 ≤ C)
    (hNC : C < N) :
    m * (C - N) < 0 ∧ 0 < m * (C + N) := by
  constructor <;> nlinarith

/-- The exterior/wedge factor factors into the positive and negative
spectral gaps. -/
theorem wedge_factorization (N C : ℝ) :
    (N - C) * (N + C) = N ^ 2 - C ^ 2 := by
  ring

/-- Exact product of the rank-two eigenvalues. -/
theorem eigenvalue_product (m N C : ℝ) :
    (m * (C - N)) * (m * (C + N)) = m ^ 2 * (C ^ 2 - N ^ 2) := by
  ring

/-- The positive PSD-distance margin is exactly `m(N-C)` when the
negative eigenvalue is `m(C-N)`. -/
theorem negative_eigenvalue_as_margin (m N C : ℝ) :
    -(m * (C - N)) = m * (N - C) := by
  ring

/-- Any scalar perturbation smaller than the exact negative margin
cannot move the negative eigenvalue through zero.  This is the scalar
core of the operator-norm Weyl perturbation step. -/
theorem perturbation_survives
    (m N C r : ℝ)
    (hr : r < m * (N - C)) :
    m * (C - N) + r < 0 := by
  nlinarith

/-- The wedge factor is strictly positive when `0 ≤ C < N`. -/
theorem wedge_positive
    (N C : ℝ)
    (hC : 0 ≤ C)
    (hNC : C < N) :
    0 < N ^ 2 - C ^ 2 := by
  nlinarith

/-- The relative negative margin `(N-C)/(N+C)` is positive under the
support-kernel hypotheses. -/
theorem relative_margin_positive
    (N C : ℝ)
    (hC : 0 ≤ C)
    (hNC : C < N) :
    0 < (N - C) / (N + C) := by
  have hnum : 0 < N - C := by linarith
  have hden : 0 < N + C := by nlinarith
  exact div_pos hnum hden

end SupportOptimalMarginFinite
end RHProof
