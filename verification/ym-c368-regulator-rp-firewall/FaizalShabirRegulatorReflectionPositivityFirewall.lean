import Mathlib

namespace Millennium.YangMills.FaizalShabirRegulatorReflectionPositivityFirewall

/-- For `0 < a < 1`, the two possible weights `1-a` and `1+a` are
strictly positive. This is the scalar shadow of a positive, reflection-
invariant reweighting. -/
theorem reweightingWeightsPositive (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < 1 - a ∧ 0 < 1 + a := by
  constructor <;> linarith

/-- On the four-point product space `{±1}²`, with reflection exchanging the
coordinates, the positive symmetric weight `R(x,y)=1-a*x*y` makes the OS
quadratic form of the test function `F(y)=y` equal to `-a`.

This formalizes only the finite arithmetic countermodel. It does not assert
that the Faizal–Shabir regulator has this form. -/
theorem reflectedSignTestFormEqualsNegA (a : ℝ) :
    (((1 - a) + (1 - a) - (1 + a) - (1 + a)) / 4) = -a := by
  ring

/-- Therefore any `a>0` in the finite countermodel gives a strictly negative
OS form despite strictly positive symmetric weights. -/
theorem positiveSymmetricReweightingCanBreakOS
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (0 < 1 - a ∧ 0 < 1 + a) ∧
      (((1 - a) + (1 - a) - (1 + a) - (1 + a)) / 4 < 0) := by
  refine ⟨reweightingWeightsPositive a ha0 ha1, ?_⟩
  rw [reflectedSignTestFormEqualsNegA]
  linarith

end Millennium.YangMills.FaizalShabirRegulatorReflectionPositivityFirewall
