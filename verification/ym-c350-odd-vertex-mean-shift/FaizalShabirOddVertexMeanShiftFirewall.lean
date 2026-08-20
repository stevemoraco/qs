import Mathlib

/-!
Finite algebraic firewall for the Yang--Mills shell-centering audit.

The source's weak chart uses a centered reference measure.  This file records
only the elementary fact that an odd perturbation of a centered reference does
not, by itself, keep the *interacting* mean centered.  It does NOT formalize
Gaussian integration, the Faizal--Shabir RG, background-field vertices, or any
Yang--Mills tadpole cancellation.
-/

namespace Millennium.YangMills.FaizalShabirOddVertexMeanShiftFirewall

/-- The symmetric two-point reference has zero mean. -/
theorem symmetricReferenceMean :
    ((((1 : ℝ) + (-1 : ℝ)) / 2)) = 0 := by
  norm_num

/-- Reweighting the symmetric two-point reference by the odd first-order factor
`1 + t X` shifts the normalized mean from zero to exactly `t`.

At `X=+1` the weight is `1+t`; at `X=-1` it is `1-t`; the total weight remains
`2`, while the weighted first moment is `2t`. -/
theorem oddTiltShiftsMean (t : ℝ) :
    (((1 + t) - (1 - t)) / 2) = t := by
  ring

/-- Therefore an odd perturbation does not imply zero interacting mean. -/
theorem nonzeroOddTiltIsNotCentered (t : ℝ) (ht : t ≠ 0) :
    (((1 + t) - (1 - t)) / 2) ≠ 0 := by
  rw [oddTiltShiftsMean]
  exact ht

/-- The same algebra isolates the first-order mean-shift coefficient: the
weighted first moment numerator is exactly `2t`. -/
theorem oddTiltFirstMomentNumerator (t : ℝ) :
    (1 + t) - (1 - t) = 2 * t := by
  ring

end Millennium.YangMills.FaizalShabirOddVertexMeanShiftFirewall