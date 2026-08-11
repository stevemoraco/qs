import Mathlib

/-!
# Scale-covariant transfer-ratio scalar core

Honesty status: elementary real identities only.  This file does not formalize
a transfer matrix, a gauge field, a Hamiltonian, reflection positivity,
Osterwalder--Schrader reconstruction, a continuum limit, or Yang--Mills theory.
-/

namespace MillenniumBraid
namespace B4YangMillsScaleCovariance

/-- An ideal one-step ratio `exp(-a*m)` has physical log-gap exactly `m`. -/
theorem idealTransferRatioMass
    (a m : ℝ) (ha : a ≠ 0) :
    -Real.log (Real.exp (-a * m)) / a = m := by
  rw [Real.log_exp]
  field_simp [ha]

/-- Exact blocking preserves the physical mass when coarse time is `b*a`. -/
theorem exactIdealBlocking
    (a b m : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    -Real.log (Real.exp (-(b * a) * m)) / (b * a) = m := by
  apply idealTransferRatioMass
  exact mul_ne_zero hb ha

/-- The sharp additive endpoint for lowering ideal mass `m` to target `mu`. -/
theorem sharpAdditiveEndpoint
    (a m mu : ℝ) :
    Real.exp (-a * m) +
        (Real.exp (-a * mu) - Real.exp (-a * m)) =
      Real.exp (-a * mu) := by
  ring

/-- The additive error `1-exp(-a*m)` moves the ideal ratio exactly to one. -/
theorem completeGapErasureEndpoint
    (a m : ℝ) :
    Real.exp (-a * m) + (1 - Real.exp (-a * m)) = 1 := by
  ring

/-- A transfer ratio equal to one has zero physical log-gap. -/
theorem unitRatioHasZeroMass
    (a : ℝ) :
    -Real.log 1 / a = 0 := by
  simp

/-- Combining the previous identities gives an exact finite gap-erasure model. -/
theorem additiveEndpointErasesIdealMass
    (a m : ℝ) :
    let ideal := Real.exp (-a * m)
    let error := 1 - ideal
    ideal + error = 1 ∧ -Real.log (ideal + error) / a = 0 := by
  dsimp
  constructor
  · ring
  · rw [show Real.exp (-a * m) + (1 - Real.exp (-a * m)) = 1 by ring]
    simp

#print axioms idealTransferRatioMass
#print axioms exactIdealBlocking
#print axioms sharpAdditiveEndpoint
#print axioms completeGapErasureEndpoint
#print axioms unitRatioHasZeroMass
#print axioms additiveEndpointErasesIdealMass

end B4YangMillsScaleCovariance
end MillenniumBraid
