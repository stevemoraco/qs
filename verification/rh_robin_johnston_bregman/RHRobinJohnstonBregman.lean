import Mathlib

namespace RHRobinJohnstonBregman

/-- The finite bookkeeping consequence of the exact analytic identity
`RobinJump = weight * JohnstonJump + BregmanSlack` with nonnegative slack. -/
theorem bregman_decomposition_domination
    (robin johnston weight slack : ℝ)
    (hdecomp : robin = weight * johnston + slack)
    (hslack : 0 ≤ slack) :
    weight * johnston ≤ robin := by
  rw [hdecomp]
  linarith

/-- With positive scale weight, a negative Robin jump can occur only when the
Johnston jump is negative. -/
theorem robin_loss_forces_johnston_loss
    (robin johnston weight slack : ℝ)
    (hweight : 0 < weight)
    (hdecomp : robin = weight * johnston + slack)
    (hslack : 0 ≤ slack)
    (hrobin : robin < 0) :
    johnston < 0 := by
  have hdom : weight * johnston ≤ robin :=
    bregman_decomposition_domination robin johnston weight slack hdecomp hslack
  by_contra hnot
  have hjnonneg : 0 ≤ johnston := le_of_not_gt hnot
  have hwj : 0 ≤ weight * johnston := mul_nonneg (le_of_lt hweight) hjnonneg
  linarith

/-- The magnitude of a negative Robin jump is bounded by the positively scaled
magnitude of the corresponding negative Johnston jump. -/
theorem robin_loss_ceiling
    (robin johnston weight slack : ℝ)
    (hweight : 0 < weight)
    (hdecomp : robin = weight * johnston + slack)
    (hslack : 0 ≤ slack)
    (hrobin : robin < 0) :
    -robin ≤ weight * (-johnston) := by
  have hdom : weight * johnston ≤ robin :=
    bregman_decomposition_domination robin johnston weight slack hdecomp hslack
  nlinarith

/-- Exact two-observable entropy ledger. If the Robin increment decomposes as
`weight * (newEnergy-oldEnergy) + slack`, then changing the correction weight
from `weight` to `nextWeight` produces the stated entropy increment. -/
theorem combined_entropy_increment
    (newRobin oldRobin newEnergy oldEnergy weight nextWeight slack : ℝ)
    (hdecomp :
      newRobin - oldRobin = weight * (newEnergy - oldEnergy) + slack) :
    (newRobin - nextWeight * newEnergy) -
        (oldRobin - weight * oldEnergy) =
      slack + (weight - nextWeight) * newEnergy := by
  calc
    (newRobin - nextWeight * newEnergy) -
        (oldRobin - weight * oldEnergy) =
        (newRobin - oldRobin) - nextWeight * newEnergy +
          weight * oldEnergy := by ring
    _ = (weight * (newEnergy - oldEnergy) + slack) -
          nextWeight * newEnergy + weight * oldEnergy := by rw [hdecomp]
    _ = slack + (weight - nextWeight) * newEnergy := by ring

/-- Positive current energy and a decreasing correction weight make an entropy
increment with nonnegative Bregman slack nonnegative. -/
theorem positive_energy_makes_entropy_monotone
    (newRobin oldRobin newEnergy oldEnergy weight nextWeight slack : ℝ)
    (hdecomp :
      newRobin - oldRobin = weight * (newEnergy - oldEnergy) + slack)
    (hslack : 0 ≤ slack)
    (hweights : nextWeight ≤ weight)
    (henergy : 0 ≤ newEnergy) :
    oldRobin - weight * oldEnergy ≤
      newRobin - nextWeight * newEnergy := by
  have hid := combined_entropy_increment
    newRobin oldRobin newEnergy oldEnergy weight nextWeight slack hdecomp
  have hnonneg : 0 ≤ slack + (weight - nextWeight) * newEnergy := by
    exact add_nonneg hslack (mul_nonneg (sub_nonneg.mpr hweights) henergy)
  linarith

#print axioms bregman_decomposition_domination
#print axioms robin_loss_forces_johnston_loss
#print axioms robin_loss_ceiling
#print axioms combined_entropy_increment
#print axioms positive_energy_makes_entropy_monotone

end RHRobinJohnstonBregman
