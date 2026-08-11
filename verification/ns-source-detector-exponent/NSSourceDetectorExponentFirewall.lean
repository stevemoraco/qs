import Mathlib

/-!
# Source-detector exponent firewall for arXiv:2606.07869v1

Honesty status: this file verifies only exact rational exponent arithmetic used
in the source-detector audit.  It does not formalize the smooth concentration
counterexample, the truncated Riesz potential, weighted lifted spaces, the
Navier--Stokes equations, or any global regularity theorem.
-/

namespace MillenniumBraid
namespace NSSourceDetectorExponentFirewall

theorem printedInterpolationIdentityFalse :
    (1 / 3 : ℚ) ≠ (1 / 9 : ℚ) * (1 / 2 : ℚ) + (8 / 9 : ℚ) * (3 / 10 : ℚ) := by
  norm_num

theorem correctInterpolationIdentity :
    (1 / 3 : ℚ) = (1 / 6 : ℚ) * (1 / 2 : ℚ) + (5 / 6 : ℚ) * (3 / 10 : ℚ) := by
  norm_num

theorem qThreeSourcePower :
    (4 : ℚ) * (3 / 2 : ℚ) = 6 := by
  norm_num

theorem hlsEndpointSourcePower :
    (4 : ℚ) * ((10 / 3 : ℚ) / ((10 / 3 : ℚ) - 1)) = 40 / 7 := by
  norm_num

theorem sourceExponentFirewall
    (q : ℝ)
    (hqOne : 1 < q)
    (hqHLS : q ≤ (10 : ℝ) / 3) :
    (40 : ℝ) / 7 ≤ 4 * q / (q - 1) := by
  have hden : 0 < q - 1 := sub_pos.mpr hqOne
  apply (le_div_iff₀ hden).2
  nlinarith [hqHLS]

theorem lThreeNormalizedCubicScaling :
    (5 : ℚ) - 3 * (5 / 3 : ℚ) = 0 := by
  norm_num

theorem lThreeNormalizedQuarticScaling :
    (5 : ℚ) - 4 * (5 / 3 : ℚ) = -(5 / 3 : ℚ) := by
  norm_num

theorem printedInterpolationValue :
    (1 / 9 : ℚ) * (1 / 2 : ℚ) + (8 / 9 : ℚ) * (3 / 10 : ℚ) = 29 / 90 := by
  norm_num

#print axioms printedInterpolationIdentityFalse
#print axioms correctInterpolationIdentity
#print axioms qThreeSourcePower
#print axioms hlsEndpointSourcePower
#print axioms sourceExponentFirewall
#print axioms lThreeNormalizedCubicScaling
#print axioms lThreeNormalizedQuarticScaling
#print axioms printedInterpolationValue

end NSSourceDetectorExponentFirewall
end MillenniumBraid
