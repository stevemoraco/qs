import Mathlib

/-!
# Finite algebra for the symmetric-translation exterior RH lane

These are only the elementary algebraic pieces of
`TRANSLATION_EXTERIOR_DEPTH_AMPLIFICATION.md`.
They do not prove RH. The analytic Laplace-pole and explicit-formula layers
are deliberately kept separate.
-/

namespace RHProof
namespace TranslationExterior

/-- After the common horizontal phases cancel, the 2-channel exterior
factor is a difference of two squared radial factors. -/
theorem symmetric_shift_wedge_factor
    (A B em ep : ℂ) :
    (A * em) * (B * em) - (A * ep) * (B * ep)
      = A * B * (em ^ 2 - ep ^ 2) := by
  ring

/-- The real algebraic sign core of the reflected-pair determinant.
In the application `s = sinh (y*c)` and `amp = |A(z)A(conj z)|`. -/
theorem reflected_pair_det_strictly_negative
    (m amp s : ℝ)
    (hm : 0 < m) (hamp : 0 < amp) (hs : 0 < s ^ 2) :
    -4 * m ^ 2 * amp ^ 2 * s ^ 2 < 0 := by
  have hp : 0 < 4 * m ^ 2 * amp ^ 2 * s ^ 2 := by
    positivity
  linarith

/-- A 2x2 Toeplitz determinant becomes negative as soon as the off-diagonal
squared magnitude exceeds the diagonal square. -/
theorem toeplitz_exterior_negative
    (h0 hc2 : ℝ)
    (hdom : h0 ^ 2 < hc2) :
    h0 ^ 2 - hc2 < 0 := by
  exact sub_neg.mpr hdom

/-- The scalar 2x2 determinant condition is exactly the squared-magnitude
bound. -/
theorem toeplitz_exterior_nonnegative_iff
    (h0 hc2 : ℝ) :
    0 ≤ h0 ^ 2 - hc2 ↔ hc2 ≤ h0 ^ 2 := by
  constructor <;> intro h <;> linarith

end TranslationExterior
end RHProof
