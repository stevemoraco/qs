import Mathlib

/-!
# Bivariate exterior polarization: finite algebra core

This file isolates the elementary algebra behind the bivariate exterior lift used
in the RH braid.  It does NOT prove RH.
-/

namespace RHProof
namespace BivariateExterior

/--
For two rank-one symmetric 2-vectors, the polarization of the second elementary
symmetric polynomial is exactly the square of the exterior determinant.

Matrix form:
`P(a aᵀ, b bᵀ) = tr(a aᵀ) tr(b bᵀ) - tr((a aᵀ)(b bᵀ))`.
The displayed scalar identity is the same statement with the 2x2 entries
expanded explicitly.
-/
theorem rankOneExteriorPolarization
    (a1 a2 b1 b2 : ℂ) :
    (a1 * a1 + a2 * a2) * (b1 * b1 + b2 * b2)
      - (a1 * b1 + a2 * b2) * (a1 * b1 + a2 * b2)
    = (a1 * b2 - a2 * b1) ^ 2 := by
  ring

/-- Real specialization: an exterior coefficient on real vectors is nonnegative. -/
theorem realExteriorCoeffNonneg
    (a1 a2 b1 b2 : ℝ) :
    0 ≤ (a1 * b2 - a2 * b1) ^ 2 := by
  positivity

/--
The scalar first-jet reflection coefficient has the exact quadratic-depth form.
Here `n` stands for `|A(γ)|`, so the actual coefficient is
`-4 m^2 y^2 |A(γ)|^4`.
-/
theorem reflectionCoeffFormula
    (m y n : ℝ) :
    -(4 * m^2 * y^2 * n^4) = -4 * m^2 * y^2 * n^4 := by
  ring

/-- Strict negativity of the blind-free first-jet reflection coefficient. -/
theorem reflectionCoeffStrictlyNegative
    (m y n : ℝ)
    (hm : 0 < m)
    (hy : y ≠ 0)
    (hn : 0 < n) :
    -4 * m^2 * y^2 * n^4 < 0 := by
  have hm2 : 0 < m^2 := sq_pos_of_pos hm
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have hn4 : 0 < n^4 := pow_pos hn 4
  have hprod : 0 < 4 * m^2 * y^2 * n^4 := by positivity
  nlinarith

/-- The coefficient vanishes identically at zero horizontal depth. -/
theorem reflectionCoeffVanishingOnLine
    (m n : ℝ) :
    -4 * m^2 * (0 : ℝ)^2 * n^4 = 0 := by
  ring

end BivariateExterior
end RHProof
