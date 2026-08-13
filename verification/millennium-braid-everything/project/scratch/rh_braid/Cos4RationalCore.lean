import Mathlib

/-!
# Finite algebra for the cos^4 rational cardinal kernel

This file machine-targets the only nontrivial rational simplification in the
explicit Fourier-transform calculation.  The analytic integration and removable
continuation are intentionally not encoded here.
-/

namespace RHProof
namespace Cos4RationalCore

/-- Rational identity obtained after integrating
`cos^4(πu/L) = (3 + 4 cos(hu) + cos(2hu))/8`, away from removable poles. -/
theorem cos4_rational_identity
    (w h : ℂ)
    (hw0 : w ≠ 0)
    (hw1 : w^2 - h^2 ≠ 0)
    (hw2 : w^2 - 4 * h^2 ≠ 0) :
    3 / (4 * w)
        - w / (w^2 - h^2)
        + w / (4 * (w^2 - 4 * h^2))
      = 3 * h^4 / (w * (w^2 - h^2) * (w^2 - 4 * h^2)) := by
  field_simp [hw0, hw1, hw2]
  ring

/-- The common-denominator numerator cancellation behind the same identity. -/
theorem cos4_numerator_cancellation (w h : ℂ) :
    3 * (w^2 - h^2) * (w^2 - 4 * h^2)
      - 4 * w^2 * (w^2 - 4 * h^2)
      + w^2 * (w^2 - h^2)
    = 12 * h^4 := by
  ring

end Cos4RationalCore
end RHProof
