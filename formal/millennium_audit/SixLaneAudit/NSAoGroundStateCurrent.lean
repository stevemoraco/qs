import Mathlib

namespace SixLaneAudit.NSAOGroundStateCurrent

/-- Real-coordinate form of the phase current `Im (conj z * z')`. -/
def phaseCurrent (a b da db : ℝ) : ℝ := a * db - b * da

/-- If `z' = -(1+i) κ ξ z`, then its phase current is
`-κ ξ |z|^2`. -/
theorem gaussian_phase_current
    (κ ξ a b da db : ℝ)
    (hda : da = -(κ * ξ) * (a - b))
    (hdb : db = -(κ * ξ) * (a + b)) :
    phaseCurrent a b da db = -(κ * ξ) * (a ^ 2 + b ^ 2) := by
  unfold phaseCurrent
  rw [hda, hdb]
  ring

/-- The same first-order system gives
`(|z|^2)' = -2 κ ξ |z|^2`. -/
theorem gaussian_normSq_derivative
    (κ ξ a b da db : ℝ)
    (hda : da = -(κ * ξ) * (a - b))
    (hdb : db = -(κ * ξ) * (a + b)) :
    2 * a * da + 2 * b * db =
      -2 * (κ * ξ) * (a ^ 2 + b ^ 2) := by
  rw [hda, hdb]
  ring

/-- Multiplication by a real radial factor contributes no new phase current:
the derivative of the factor cancels exactly. -/
theorem real_multiplier_phase_current
    (s ds a b da db : ℝ) :
    phaseCurrent (s * a) (s * b)
        (ds * a + s * da) (ds * b + s * db) =
      s ^ 2 * phaseCurrent a b da db := by
  unfold phaseCurrent
  ring

/-- Differentiating `j = -κ ξ q` together with
`q' = -2 κ ξ q` gives the explicit feedback profile. -/
theorem gaussian_feedback_profile
    (κ ξ q q' j j' : ℝ)
    (hq' : q' = -2 * κ * ξ * q)
    (hj : j = -κ * ξ * q)
    (hj' : j' = -κ * q - κ * ξ * q') :
    -j' = κ * (1 - 2 * κ * ξ ^ 2) * q := by
  rw [hq'] at hj'
  nlinarith

/-- The center coefficient of the leading feedback is strictly positive. -/
theorem center_feedback_positive
    (g κ q : ℝ) (hg : 0 < g) (hκ : 0 < κ) (hq : 0 < q) :
    0 < g * κ * q := by
  exact mul_pos (mul_pos hg hκ) hq

#print axioms gaussian_phase_current
#print axioms gaussian_normSq_derivative
#print axioms real_multiplier_phase_current
#print axioms gaussian_feedback_profile
#print axioms center_feedback_positive

end SixLaneAudit.NSAOGroundStateCurrent
