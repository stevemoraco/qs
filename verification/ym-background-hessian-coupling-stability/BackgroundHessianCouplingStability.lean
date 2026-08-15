import Mathlib

/-!
# Fixed-scale background-Hessian coupling stability

This file isolates finite scalar algebra behind a load-bearing Yang--Mills
continuum-coupling typing step.

In the audited Kirk-v4 source, the local standard/background coupling at a
nonexceptional retained momentum is defined as the inverse of one scalar
projected background Hessian.  Therefore a continuum coupling landing at one
fixed physical UV reference scale can be reduced to convergence of that single
positive scalar Hessian, provided its scheme interpretation is proved
separately.

The statements below prove only the elementary stability of inversion near a
strictly positive limiting Hessian.  They do not prove convergence of any
Yang--Mills background Hessian, identify a renormalization scheme, prove a beta
function, define Lambda_YM, construct an OS limit, or prove a mass gap.
-/

namespace Millennium.YangMills

/-- If a regulated scalar Hessian lies within half of a strictly positive
limiting Hessian, then it lies in the explicit interval `[H/2, 3H/2]`. -/
theorem backgroundHessian_halfError_bounds
    {H Hn : ℝ}
    (hH : 0 < H)
    (herr : |Hn - H| ≤ H / 2) :
    H / 2 ≤ Hn ∧ Hn ≤ 3 * H / 2 := by
  have habs : -(H / 2) ≤ Hn - H ∧ Hn - H ≤ H / 2 := abs_le.mp herr
  constructor <;> linarith

/-- The same half-error hypothesis prevents the regulated Hessian denominator
from crossing zero. -/
theorem backgroundHessian_positive_of_halfError
    {H Hn : ℝ}
    (hH : 0 < H)
    (herr : |Hn - H| ≤ H / 2) :
    0 < Hn := by
  have hb := backgroundHessian_halfError_bounds hH herr
  linarith

/-- Exact difference identity for the inverse-coupling coordinate. -/
theorem inverseHessian_difference_identity
    {H Hn : ℝ}
    (hH : H ≠ 0)
    (hHn : Hn ≠ 0) :
    1 / Hn - 1 / H = (H - Hn) / (Hn * H) := by
  field_simp [hH, hHn]

/-- Under the half-error hypothesis, the positive denominator in the inverse
coupling difference is bounded below by `H^2/2`. -/
theorem inverseHessian_denominator_lower
    {H Hn : ℝ}
    (hH : 0 < H)
    (herr : |Hn - H| ≤ H / 2) :
    H ^ 2 / 2 ≤ Hn * H := by
  have hb := backgroundHessian_halfError_bounds hH herr
  have hH0 : 0 ≤ H := le_of_lt hH
  have hmul := mul_le_mul_of_nonneg_right hb.1 hH0
  nlinarith

#print axioms backgroundHessian_halfError_bounds
#print axioms backgroundHessian_positive_of_halfError
#print axioms inverseHessian_difference_identity
#print axioms inverseHessian_denominator_lower

end Millennium.YangMills
