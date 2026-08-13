import Mathlib

/-!
# Ring-mode feedback energy-sign scalar firewall

This file formalizes only the scalar wave/parent energy-transfer identity used
in the round-42 Navier--Stokes audit. It does not formalize Euler or
Navier--Stokes fields, Leray projection, cylindrical modes, phase averaging,
integration by parts, or vortex-column instability.
-/

namespace MillenniumBraid
namespace B2Round42NSRing

/-- Positive exponential growth and positive perturbation energy give a
strictly positive wave-energy gain. -/
theorem growing_wave_gain_positive
    {growth energy : ℝ}
    (hgrowth : 0 < growth) (henergy : 0 < energy) :
    0 < growth * energy := by
  positivity

/-- If parent feedback work is the negative of wave-energy gain, it is
strictly negative. -/
theorem feedback_work_strictly_negative
    {growth energy feedbackWork : ℝ}
    (hgrowth : 0 < growth) (henergy : 0 < energy)
    (hfeedback : feedbackWork = -(growth * energy)) :
    feedbackWork < 0 := by
  rw [hfeedback]
  exact neg_neg_of_pos (mul_pos hgrowth henergy)

/-- Exact quadratic exchange ledger: wave gain plus parent reaction work is
zero. -/
theorem wave_gain_plus_parent_work_zero
    (growth energy : ℝ) :
    growth * energy + (-(growth * energy)) = 0 := by
  ring

/-- Packaged sign correction for a nonzero unstable mode. -/
theorem unstable_mode_feedback_is_reaction
    {growth energy waveGain parentWork : ℝ}
    (hgrowth : 0 < growth) (henergy : 0 < energy)
    (hwave : waveGain = growth * energy)
    (hparent : parentWork = -waveGain) :
    0 < waveGain ∧ parentWork < 0 ∧ waveGain + parentWork = 0 := by
  have hgain : 0 < waveGain := by
    rw [hwave]
    exact mul_pos hgrowth henergy
  constructor
  · exact hgain
  constructor
  · rw [hparent]
    exact neg_neg_of_pos hgain
  · rw [hparent]
    ring

#print axioms growing_wave_gain_positive
#print axioms feedback_work_strictly_negative
#print axioms wave_gain_plus_parent_work_zero
#print axioms unstable_mode_feedback_is_reaction

end B2Round42NSRing
end MillenniumBraid
