import Mathlib

namespace NSDynamicSchurEnergy

/-- Abstract integrated energy accounting for an exterior equation
`b_t + L b = -S`.  Here `initialEnergy = ‖b(0)‖²`,
`terminalEnergy = ‖b(T)‖²`, `dissipation = ∫ ⟪Lb,b⟫`, and
`feedback = ∫ ⟪S,b⟫`. -/
theorem feedback_bounded_by_initial_exterior_energy
    (initialEnergy terminalEnergy dissipation feedback : ℝ)
    (hterminal : 0 ≤ terminalEnergy)
    (hdissipation : 0 ≤ dissipation)
    (hidentity :
      feedback = initialEnergy / 2 - terminalEnergy / 2 - dissipation) :
    feedback ≤ initialEnergy / 2 := by
  linarith

/-- With zero initial exterior data, the complete time-integrated active/exterior
feedback pairing is nonpositive. -/
theorem zero_initial_feedback_nonpositive
    (terminalEnergy dissipation feedback : ℝ)
    (hterminal : 0 ≤ terminalEnergy)
    (hdissipation : 0 ≤ dissipation)
    (hidentity : feedback = -terminalEnergy / 2 - dissipation) :
    feedback ≤ 0 := by
  linarith

/-- The feedback is strictly dissipative as soon as either terminal exterior
energy or integrated exterior dissipation is positive. -/
theorem zero_initial_feedback_strictly_negative
    (terminalEnergy dissipation feedback : ℝ)
    (hterminal : 0 ≤ terminalEnergy)
    (hdissipation : 0 ≤ dissipation)
    (hnontrivial : 0 < terminalEnergy ∨ 0 < dissipation)
    (hidentity : feedback = -terminalEnergy / 2 - dissipation) :
    feedback < 0 := by
  rcases hnontrivial with hterminalPos | hdissipationPos <;> linarith

/-- Exact total-energy consequence for a skew active/exterior coupling: if the
active-to-exterior transfer cancels in the total energy identity, total energy
can only decrease by the nonnegative exterior dissipation. -/
theorem coupled_total_energy_nonincrease
    (initialTotal terminalTotal dissipation : ℝ)
    (hdissipation : 0 ≤ dissipation)
    (hidentity : terminalTotal = initialTotal - 2 * dissipation) :
    terminalTotal ≤ initialTotal := by
  linarith

/-- A strict loss occurs whenever the exterior dissipation is nonzero. -/
theorem coupled_total_energy_strict_decrease
    (initialTotal terminalTotal dissipation : ℝ)
    (hdissipation : 0 < dissipation)
    (hidentity : terminalTotal = initialTotal - 2 * dissipation) :
    terminalTotal < initialTotal := by
  linarith

end NSDynamicSchurEnergy
