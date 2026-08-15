import Mathlib

/-!
# Fixed weak coupling window

Finite scalar firewall for a Yang--Mills dimensional-transmutation comparison.

Suppose an operational weak coupling `u` is already trapped in one positive
compact interval `[uMin,uMax]`, and a second coupling coordinate `v` differs by
a uniform quadratic finite-scheme error

    |v-u| <= C*u^2.

If the weak interval is chosen so that `C*uMax <= 1/2`, then `v` remains in the
explicit positive compact interval `[uMin/2, 3*uMax/2]`.

This is the finite algebra needed after the source-specific Kirk-v4 backward
shooting bound at one fixed number of dyadic steps from first crossing.  It does
not prove that the source coupling satisfies the hypotheses, identify a
renormalization scheme, construct Lambda_YM, prove an OS limit, or prove a mass
gap.
-/

namespace Millennium.YangMills

/-- A uniform `O(u^2)` unit-tangent scheme error preserves a positive compact
weak-coupling window, with explicit constants. -/
theorem approximateIdentity_preserves_positive_window
    {u v uMin uMax C : ℝ}
    (huMin : 0 < uMin)
    (hu : uMin ≤ u)
    (huMax : u ≤ uMax)
    (hC : 0 ≤ C)
    (hsmall : C * uMax ≤ 1 / 2)
    (herr : |v - u| ≤ C * u ^ 2) :
    uMin / 2 ≤ v ∧ v ≤ 3 * uMax / 2 := by
  have hu0 : 0 ≤ u := by linarith
  have hCu : C * u ≤ 1 / 2 := by
    have hmono : C * u ≤ C * uMax :=
      mul_le_mul_of_nonneg_left huMax hC
    linarith
  have hquad : C * u ^ 2 ≤ u / 2 := by
    nlinarith
  have habs : -(C * u ^ 2) ≤ v - u ∧ v - u ≤ C * u ^ 2 :=
    (abs_le.mp herr)
  constructor
  · nlinarith
  · nlinarith

/-- The same hypotheses force the transformed coupling to stay strictly
positive, so a fixed-scale inverse/background coordinate cannot cross zero. -/
theorem approximateIdentity_positive
    {u v uMin uMax C : ℝ}
    (huMin : 0 < uMin)
    (hu : uMin ≤ u)
    (huMax : u ≤ uMax)
    (hC : 0 ≤ C)
    (hsmall : C * uMax ≤ 1 / 2)
    (herr : |v - u| ≤ C * u ^ 2) :
    0 < v := by
  have hwin := approximateIdentity_preserves_positive_window
    huMin hu huMax hC hsmall herr
  linarith

#print axioms approximateIdentity_preserves_positive_window
#print axioms approximateIdentity_positive

end Millennium.YangMills
