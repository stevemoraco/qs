import Mathlib

namespace RHSuzukiScrewDyadic

/-- If `I(a)=g(a)+r(a)-8` at scale `a` and
`I(2a)=g(2a)+r(2a)-8`, then the two-scale deficit is the corresponding
dyadic screw increment plus the correction difference. -/
theorem dyadic_deficit_algebra
    {ga g2a ra r2a a delta : ℝ}
    (hdelta : delta = (ga + ra - 8) - (g2a + r2a - 8) - 2 * a) :
    delta = ga - g2a - 2 * a + ra - r2a := by
  linarith

/-- Rewriting with `F=-g` converts the screw difference into a forward dyadic
increment of `F`. -/
theorem negative_screw_increment
    {ga g2a a ra r2a delta : ℝ}
    (h : delta = ga - g2a - 2 * a + ra - r2a) :
    delta = (-g2a) - (-ga) - 2 * a + ra - r2a := by
  linarith

/-- Normalized dyadic increment identity:
if `F(a)=a H(a)` and `F(2a)=2a H(2a)`, then
`F(2a)-F(a)=a(2H(2a)-H(a))`. -/
theorem normalized_dyadic_increment
    {a Ha H2a : ℝ} :
    (2 * a) * H2a - a * Ha = a * (2 * H2a - Ha) := by
  ring

/-- Eventual sign alone cannot algebraically force a positive dyadic increment:
there is a nonnegative constant countermodel. -/
theorem nonnegative_constant_has_zero_increment
    {c : ℝ} (hc : 0 <= c) :
    0 <= c ∧ c - c = 0 := by
  constructor
  · exact hc
  · ring

#print axioms dyadic_deficit_algebra
#print axioms negative_screw_increment
#print axioms normalized_dyadic_increment
#print axioms nonnegative_constant_has_zero_increment

end RHSuzukiScrewDyadic
