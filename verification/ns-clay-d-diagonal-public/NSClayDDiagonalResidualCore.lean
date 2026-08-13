import Mathlib

namespace NSClayDDiagonalResidualCore

/-- If the WKB correction depth `m` beats the polynomial derivative loss `P`
by two powers after multiplication by the ratio exponent `b-1`, then the
remaining shell exponent is at most `-2`. -/
theorem diagonal_exponent_margin
    {b P m : ℝ}
    (hmargin : P + 2 ≤ (b - 1) * m) :
    P - (b - 1) * m ≤ -2 := by
  linarith

/-- A stronger shellwise margin implies any weaker target margin. -/
theorem diagonal_margin_monotone
    {b P m r : ℝ}
    (hr : 0 ≤ r)
    (hmargin : P + r ≤ (b - 1) * m) :
    P - (b - 1) * m ≤ -r := by
  linarith

/-- The adjacent ratio exponent identity for a power-law shell hierarchy:
`N^(b-1)` raised to correction depth `m` contributes exponent
`-(b-1)m`, which combines with polynomial loss `P`. -/
theorem ratio_exponent_identity (b P m : ℝ) :
    P + (-(b - 1) * m) = P - (b - 1) * m := by
  ring

#check diagonal_exponent_margin
#print axioms diagonal_exponent_margin
#print axioms diagonal_margin_monotone
#print axioms ratio_exponent_identity

end NSClayDDiagonalResidualCore
