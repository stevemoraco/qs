import Mathlib

/-!
# Exact finite/scalar survivors from the semantic Millennium CEGIS run

This public replay formalizes only two elementary consequences isolated by the
executable counterexample-guided search. It does not formalize any official
Millennium endpoint.
-/

namespace Millennium.Crosslane.CEGISFiniteSurvivors

/-- Three-side valuation closure for a determinant square. -/
theorem bsd_three_side_square
    (hTop hBot vLeft vRight : ℤ)
    (hSquare : vRight - vLeft = hBot - hTop)
    (hHorizontal : hBot = hTop)
    (hLeft : vLeft = 0) :
    vRight = 0 := by
  omega

/-- Absolute, rather than oriented-positive, RSS correlation suffices for the
finite-energy terminal bound. -/
theorem ns_absolute_correlation_terminal
    (u v corr theta c R E : ℝ)
    (hu : 0 ≤ u)
    (hv : 0 < v)
    (hTheta : 0 ≤ theta)
    (hCauchy : |corr| ≤ u * v)
    (hCorrelation : theta * v ^ 2 ≤ |corr|)
    (hShell : c * R ≤ v ^ 2)
    (hEnergy : u ^ 2 ≤ E) :
    theta ^ 2 * c * R ≤ E := by
  have hThetaV2 : theta * v ^ 2 ≤ u * v :=
    le_trans hCorrelation hCauchy
  have hThetaV : theta * v ≤ u := by
    nlinarith
  have hThetaVNonneg : 0 ≤ theta * v :=
    mul_nonneg hTheta hv.le
  have hSquare : (theta * v) ^ 2 ≤ u ^ 2 := by
    nlinarith [sq_nonneg (u - theta * v)]
  have hScaledShell : theta ^ 2 * (c * R) ≤ theta ^ 2 * v ^ 2 :=
    mul_le_mul_of_nonneg_left hShell (sq_nonneg theta)
  calc
    theta ^ 2 * c * R = theta ^ 2 * (c * R) := by ring
    _ ≤ theta ^ 2 * v ^ 2 := hScaledShell
    _ = (theta * v) ^ 2 := by ring
    _ ≤ u ^ 2 := hSquare
    _ ≤ E := hEnergy

#print axioms bsd_three_side_square
#print axioms ns_absolute_correlation_terminal

end Millennium.Crosslane.CEGISFiniteSurvivors
