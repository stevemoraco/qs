import Mathlib

/-!
Finite algebraic firewalls for the Yang--Mills two-loop scheme-matching audit.

These declarations formalize only coefficient cancellations under an analytic
single-coupling reparametrization tangent to the identity. They do NOT
formalize the Faizal--Shabir RG, perturbative Yang--Mills beta-function
calculations, or the existence of the required centered shell coupling.
-/

namespace Millennium.YangMills.FaizalShabirTwoLoopSchemeInvarianceFirewall

/-- The two-loop beta coefficient survives a cubic coupling reparametrization:
the chain-rule contribution and the inverse-coordinate contribution cancel. -/
theorem continuousTwoLoopCoefficientInvariant
    (b0 b1 s : ℝ) :
    (b1 + 3 * s * b0) - 3 * s * b0 = b1 := by
  ring

/-- For a finite RG step `g ↦ g - a g^3 + c g^5 + O(g^7)`, the fifth-order
coefficient is unchanged by an odd analytic reparametrization
`u = g + s g^3 + t g^5 + O(g^7)`.  This theorem records the exact coefficient
cancellation after inversion and re-expansion through degree five. -/
theorem finiteStepFifthOrderCoefficientInvariant
    (a c s t : ℝ) :
    (3 * s^2 - t + 3 * a * s + c) - 3 * s * (s + a) + t = c := by
  ring

/-- The inverse-square coordinate changes by a finite constant at leading order
under `u = g (1 + s g^2)`: after clearing the common `g^2` factor, the exact
numerator is `-(2s + s^2 g^2)`. -/
theorem inverseSquareSchemeShiftNumerator
    (g s : ℝ) :
    1 - (1 + s * g^2)^2 = -(2 * s + s^2 * g^2) * g^2 := by
  ring

/-- Pure-Yang--Mills universal ratio in the conventional coefficients with the
common group/loop factor canceled. -/
theorem pureYMUniversalTwoLoopRatio :
    (((34 : ℝ) / 3) / (2 * (((11 : ℝ) / 3)^2))) = (51 : ℝ) / 121 := by
  norm_num

end Millennium.YangMills.FaizalShabirTwoLoopSchemeInvarianceFirewall
