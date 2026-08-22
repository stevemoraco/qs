import Mathlib

/-!
# Finite algebra for blind-point-free exterior detectors

This file proves only elementary real-algebra statements used by the
asymmetric/Hermite/Christoffel-Darboux depth-sensitive lane. It makes no
statement about zeta zeros or RH.
-/

namespace RHProof
namespace HermiteExteriorFinite

/-- The determinant of the real-part reflection-pair matrix is minus four
    times the square of the 2D exterior product. -/
theorem pair_det_identity
    (ar ai br bi : ℝ) :
    4 * ((ar^2 - ai^2) * (br^2 - bi^2)
      - (ar * br - ai * bi)^2)
      = -4 * (ai * br - ar * bi)^2 := by
  ring

/-- Universal asymmetric two-vector identity in real coordinates.

Let `u=(a,b)` and `w=(c,d)` in `ℂ²`, with the eight arguments below their
real and imaginary parts.  The left side is
`det (u w* + w u*)`; the right side is `-|det[u,w]|²`.
-/
theorem asymmetric_pair_det_identity
    (ar ai br bi cr ci dr di : ℝ) :
    (2 * (ar * cr + ai * ci)) * (2 * (br * dr + bi * di))
      - ((ar * dr + ai * di + cr * br + ci * bi)^2
        + (ai * dr - ar * di + ci * br - cr * bi)^2)
      = - (((ar * dr - ai * di) - (br * cr - bi * ci))^2
        + ((ar * di + ai * dr) - (br * ci + bi * cr))^2) := by
  ring

/-- For `p(z)=z` and `q(z)=z²-1`, the imaginary exterior factor is
    `-y (x²+y²+1)`. -/
theorem hermite12_exterior_factor
    (x y : ℝ) :
    y * (x^2 - y^2 - 1) - 2 * x^2 * y
      = -y * (x^2 + y^2 + 1) := by
  ring

/-- The corresponding reflection-pair determinant has the exact factorization
    `-4 y² (x²+y²+1)²`. -/
theorem hermite12_pair_det
    (x y : ℝ) :
    -4 * (-y * (x^2 + y^2 + 1))^2
      = -4 * y^2 * (x^2 + y^2 + 1)^2 := by
  ring

/-- The unscaled Hermite `He₁/He₂` pair is strictly negative at every nonzero
    vertical depth. -/
theorem hermite12_strict_negative
    (x y : ℝ) (hy : y ≠ 0) :
    -4 * y^2 * (x^2 + y^2 + 1)^2 < 0 := by
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have hpos : 0 < x^2 + y^2 + 1 := by positivity
  nlinarith [sq_pos_of_pos hpos]

/-- Multiplying by any strictly positive common scale preserves strict
    negativity. This abstracts the positive factor `m² |A(z)|⁴`. -/
theorem hermite12_scaled_strict_negative
    (x y scale : ℝ) (hy : y ≠ 0) (hscale : 0 < scale) :
    -4 * scale * y^2 * (x^2 + y^2 + 1)^2 < 0 := by
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have hpos : 0 < x^2 + y^2 + 1 := by positivity
  have hsq : 0 < (x^2 + y^2 + 1)^2 := sq_pos_of_pos hpos
  positivity

/-- Abstract finite sign core for the Christoffel-Darboux detector.

If `K>0` is the diagonal CD kernel, `a>0` the Jacobi recurrence coefficient,
`scale>0` the common positive Weil/window factor, and `y ≠ 0` the off-line
depth, then the exact determinant `-4*scale*(y*K/a)^2` is strictly negative.
-/
theorem christoffel_darboux_scaled_strict_negative
    (y K a scale : ℝ)
    (hy : y ≠ 0) (hK : 0 < K) (ha : 0 < a) (hscale : 0 < scale) :
    -4 * scale * (y * K / a)^2 < 0 := by
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hquot : 0 < (y * K / a)^2 := by
    rw [div_pow]
    positivity
  positivity

end HermiteExteriorFinite
end RHProof
