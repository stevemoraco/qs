import Mathlib

/-!
# Navier--Stokes amplitude-local VMO scale ledger

Honesty status: this file formalizes only finite real/rational arithmetic used
in the amplitude-local restricted-commutator criterion and its critical packet
obstruction.  It does not formalize Calderón--Zygmund operators, Lorentz spaces,
the strain commutator, the Navier--Stokes equations, the conditional regularity
theorem, or the Clay statement.
-/

namespace MillenniumBraid
namespace NSAmplitudeLocalVMOScaleLedger

theorem lowSourceLorentzExponent :
    (1 : ℚ) - (3 / 2 : ℚ) / 3 = 1 / 2 := by
  norm_num

theorem criticalFarKernelExponent :
    (3 : ℚ) / (3 / 2 : ℚ) = 2 := by
  norm_num

theorem weakVorticityScalingExponent :
    (1 : ℚ) - (3 / 2 : ℚ) / (3 / 2 : ℚ) = 0 := by
  norm_num

theorem kineticEnergySquareScalingExponent :
    (1 : ℚ) - (3 / 2 : ℚ) = -(1 / 2 : ℚ) := by
  norm_num

theorem admissibleAmplitudeScaleExponents
    (theta a : ℝ)
    (htheta0 : 0 < theta)
    (htheta1 : theta < 1)
    (ha0 : 0 < a)
    (ha1 : a < 1 / 2) :
    0 < 1 - 2 * a ∧
    0 < (1 - theta) / 2 ∧
    0 < 1 / 2 - a := by
  constructor
  · linarith
  constructor <;> linarith

theorem oppositeDirectionsOscillation (c : ℝ) :
    2 ≤ |(1 : ℝ) - c| + |(-1 : ℝ) - c| := by
  have hplus : 1 - c ≤ |(1 : ℝ) - c| := le_abs_self (1 - c)
  have hminusRaw : -((-1 : ℝ) - c) ≤ |(-1 : ℝ) - c| := neg_le_abs ((-1 : ℝ) - c)
  have hminus : 1 + c ≤ |(-1 : ℝ) - c| := by
    linarith
  linarith

theorem oppositeCoreMeanLowerBound
    (kappa c : ℝ)
    (hkappa : 0 ≤ kappa) :
    2 * kappa ≤
      kappa * |(1 : ℝ) - c| + kappa * |(-1 : ℝ) - c| := by
  have h := mul_le_mul_of_nonneg_left (oppositeDirectionsOscillation c) hkappa
  nlinarith

theorem packetToLocalizationExponentIdentity (a : ℝ) :
    1 / 2 - a = (1 - 2 * a) / 2 := by
  ring

theorem threeTermErrorBudget
    (near far low epsilon : ℝ)
    (hnear : near ≤ epsilon / 3)
    (hfar : far ≤ epsilon / 3)
    (hlow : low ≤ epsilon / 3) :
    near + far + low ≤ epsilon := by
  linarith

#print axioms lowSourceLorentzExponent
#print axioms criticalFarKernelExponent
#print axioms weakVorticityScalingExponent
#print axioms kineticEnergySquareScalingExponent
#print axioms admissibleAmplitudeScaleExponents
#print axioms oppositeDirectionsOscillation
#print axioms oppositeCoreMeanLowerBound
#print axioms packetToLocalizationExponentIdentity
#print axioms threeTermErrorBudget

end NSAmplitudeLocalVMOScaleLedger
end MillenniumBraid
