import Mathlib

namespace NSIntermittentStressEnergyMatch

/-- Exponent identity for pointwise stress amplitude times intermittent volume. -/
theorem l1_energy_exponent (alpha : ℝ) :
    2*(alpha-1) + (-2*(alpha-1)) = 0 := by ring

/-- Exponent identity for the L2 stress size after multiplying by sqrt(volume). -/
theorem l2_stress_exponent (alpha : ℝ) :
    2*(alpha-1) - (alpha-1) = alpha-1 := by ring

/-- One parent derivative upgrades the L2 stress exponent to the Palasek force exponent. -/
theorem force_exponent (alpha : ℝ) :
    1 + (alpha-1) = alpha := by ring

/-- Three-dimensional blob linear-scale exponent. -/
theorem blob_linear_exponent (alpha : ℝ) :
    (-2*(alpha-1))/3 = -(2*(alpha-1)/3) := by ring

/-- The strict 3D modulation slack is positive exactly below the physical endpoint 5/2. -/
theorem modulation_slack_iff {alpha : ℝ} :
    0 < 1 - 2*(alpha-1)/3 ↔ alpha < (5:ℝ)/2 := by
  constructor <;> intro h <;> linarith

#print axioms l1_energy_exponent
#print axioms l2_stress_exponent
#print axioms force_exponent
#print axioms blob_linear_exponent
#print axioms modulation_slack_iff

end NSIntermittentStressEnergyMatch
