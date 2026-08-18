import Mathlib

namespace RHB345ZeroTypeShiftFinite

/-- Exact scalar identity behind the B345A shifted anchored-edge extraction. -/
theorem shiftedAnchoredEdgeEnergyIdentity
    (Fx Fy Fxy lambda : ℝ) :
    (2 * Fx + lambda) + (2 * Fy + lambda)
      - 2 * (Fx + Fy - Fxy)
      = 2 * (Fxy + lambda) := by
  ring

/-- A nonnegative shifted anchored edge quadratic forces the shifted pair defect nonnegative. -/
theorem shiftedPairDefectNonnegative
    {Fx Fy Fxy lambda : ℝ}
    (hquad : 0 ≤ (2 * Fx + lambda) + (2 * Fy + lambda)
      - 2 * (Fx + Fy - Fxy)) :
    0 ≤ Fxy + lambda := by
  rw [shiftedAnchoredEdgeEnergyIdentity] at hquad
  linarith

/-- The B345 shift is a strict finite-data weakening of zero threshold. -/
theorem zeroTypeShiftStrictlyWeakensZeroThreshold
    {lambda : ℝ} (hlambda : 0 < lambda) :
    -lambda / 2 < 0 ∧ 0 < -lambda / 2 + lambda := by
  constructor <;> linarith

/-- Shifted pairwise signs still do not force the shifted anchored 2x2 matrix PSD. -/
theorem shiftedPairwiseSignsDoNotForceAnchoredPSD :
    (0 : ℚ) < 1 ∧
    (0 : ℚ) < 2 + 1 ∧
    (1 : ℚ) * 1 - (-2 : ℚ) ^ 2 < 0 := by
  norm_num

#print axioms shiftedAnchoredEdgeEnergyIdentity
#print axioms shiftedPairDefectNonnegative
#print axioms zeroTypeShiftStrictlyWeakensZeroThreshold
#print axioms shiftedPairwiseSignsDoNotForceAnchoredPSD

end RHB345ZeroTypeShiftFinite
