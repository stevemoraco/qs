import Mathlib

/-!
# Yu annular Poincare scale cancellation — finite algebra only

This file formalizes one scalar inequality used in the current audit of the
filtered far-field route for three-dimensional Navier--Stokes.

It does **not** formalize Yu's PDE estimates, annular Poincare inequalities,
filtered vorticity, harmonic jets, Navier--Stokes regularity, or blow-up.
-/

namespace NSYuDyadicPoincareWeightCancellation

/-- If a shell Poincare estimate has the scale `rj * G` and the reassignment
weight `w` satisfies `w * rj = rk`, then multiplying by the reassignment weight
moves the derivative term exactly to the core scale `rk`, with no residual
power of the shell/core ratio. -/
theorem weighted_poincare_scale_cancellation
    (w rj rk A2 G B2 C : ℝ)
    (hw : 0 ≤ w)
    (hscale : w * rj = rk)
    (hpoincare : A2 ≤ C * rj * G + B2) :
    w * A2 ≤ C * rk * G + w * B2 := by
  calc
    w * A2 ≤ w * (C * rj * G + B2) :=
      mul_le_mul_of_nonneg_left hpoincare hw
    _ = C * (w * rj) * G + w * B2 := by ring
    _ = C * rk * G + w * B2 := by rw [hscale]

/-- The exact dyadic specialization: if `rj = 2^m * rk` is encoded through a
nonnegative weight `w` satisfying `w*rj=rk`, no scale loss remains on the
fluctuation/gradient currency. -/
theorem dyadic_reassignment_has_no_extra_gradient_scale_loss
    (w rj rk fluctSq gradBudget lowModeSq C : ℝ)
    (hw : 0 ≤ w)
    (hdyadic : w * rj = rk)
    (hP : fluctSq ≤ C * rj * gradBudget + lowModeSq) :
    w * fluctSq ≤ C * rk * gradBudget + w * lowModeSq := by
  exact weighted_poincare_scale_cancellation
    w rj rk fluctSq gradBudget lowModeSq C hw hdyadic hP

/-- Poincare decomposition does not by itself remove the low-mode remainder:
there are nonnegative data with zero derivative budget and strictly positive
low-mode and shell mass.  This is the finite firewall preventing the scale
cancellation theorem from being misread as complete annular closure. -/
theorem positive_low_mode_can_survive_zero_gradient_budget :
    ∃ fluctSq gradBudget lowModeSq C : ℝ,
      0 ≤ gradBudget ∧ 0 < lowModeSq ∧
      fluctSq ≤ C * gradBudget + lowModeSq ∧ 0 < fluctSq := by
  refine ⟨1, 0, 1, 1, ?_⟩
  norm_num

#print axioms weighted_poincare_scale_cancellation
#print axioms dyadic_reassignment_has_no_extra_gradient_scale_loss
#print axioms positive_low_mode_can_survive_zero_gradient_budget

end NSYuDyadicPoincareWeightCancellation
