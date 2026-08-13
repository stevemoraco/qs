import Mathlib

namespace PNPMCSPRestrictionTransformerFirewall

/-- Pure logical Shannon-reconstruction contrapositive: if low complexity of every
restriction would upper-bound the source, then a source above that reconstruction
budget has a hard restriction. -/
theorem hard_source_forces_hard_restriction
    {ι : Type*}
    (restrictionCost : ι → ℝ)
    {sourceCost q targetThreshold overhead : ℝ}
    (hReconstruct :
      (∀ i, restrictionCost i ≤ targetThreshold) →
        sourceCost ≤ q * (targetThreshold + overhead))
    (hHard : q * (targetThreshold + overhead) < sourceCost) :
    ∃ i, targetThreshold < restrictionCost i := by
  by_contra h
  push_neg at h
  have hUpper := hReconstruct h
  linarith

/-- The NO-side restriction threshold exponent. -/
theorem restriction_threshold_exponent_identity
    (lambda muLow : ℝ) :
    (1 - lambda) + muLow * lambda = 1 - lambda * (1 - muLow) := by
  ring

/-- Choosing the retained-variable fraction above the threshold-matching ratio
makes the reconstructed exponent smaller than the source hard exponent. -/
theorem restriction_fraction_transfers_hard_side
    {lambda muLow muHigh : ℝ}
    (hmuLow : muLow < 1)
    (hlambda : (1 - muHigh) / (1 - muLow) < lambda) :
    1 - lambda + muLow * lambda < muHigh := by
  have hden : 0 < 1 - muLow := sub_pos.mpr hmuLow
  have hmul : 1 - muHigh < lambda * (1 - muLow) :=
    (div_lt_iff₀ hden).mp hlambda
  nlinarith

/-- Enumerating all fixed-prefix restrictions and running an `M^(1+epsilon)`
algorithm has total truth-table exponent `1 + lambda*epsilon`. -/
theorem restriction_enumeration_time_exponent
    (lambda epsilon : ℝ) :
    (1 - lambda) + (1 + epsilon) * lambda = 1 + lambda * epsilon := by
  ring

/-- The interval between the NO-transfer lower bound and the source-threshold
upper bound is nonempty exactly under the displayed product inequality. -/
theorem restriction_window_nonempty_iff
    {muLow muHigh : ℝ}
    (hmuLow : muLow < 1) :
    (1 - muHigh) / (1 - muLow) < muHigh ↔
      1 < muHigh * (2 - muLow) := by
  have hden : 0 < 1 - muLow := sub_pos.mpr hmuLow
  constructor
  · intro h
    have hmul : 1 - muHigh < muHigh * (1 - muLow) :=
      (div_lt_iff₀ hden).mp h
    nlinarith
  · intro h
    apply (div_lt_iff₀ hden).2
    nlinarith

/-- Abstract YES/NO promise predicates for a complexity cost. -/
def SourceYes (cost threshold : ℝ) : Prop := cost ≤ threshold

def TargetNo (cost threshold : ℝ) : Prop := threshold ≤ cost

/-- If an ignored-variable extension and every restriction have the same cost,
a cost between the source YES and target NO thresholds is simultaneously source-low
and target-high for every restriction. -/
theorem ignored_variable_promise_collision
    {ι : Type*}
    {gCost sourceYesThreshold targetNoThreshold : ℝ}
    (hSource : gCost ≤ sourceYesThreshold)
    (hTarget : targetNoThreshold ≤ gCost) :
    SourceYes gCost sourceYesThreshold ∧
      ∀ _i : ι, TargetNo gCost targetNoThreshold := by
  exact ⟨hSource, fun _ => hTarget⟩

/-- Extension and restriction inequalities force exact dummy-variable complexity
preservation. -/
theorem extension_restriction_cost_equality
    {baseCost extensionCost : ℝ}
    (hIgnore : extensionCost ≤ baseCost)
    (hRestrict : baseCost ≤ extensionCost) :
    extensionCost = baseCost := by
  exact le_antisymm hIgnore hRestrict

/-- If the target NO threshold lies above the source YES threshold, the collision
interval is empty; otherwise promise preservation needs an additional theorem. -/
theorem promise_collision_interval_empty_of_separated_thresholds
    {gCost sourceYesThreshold targetNoThreshold : ℝ}
    (hSeparated : sourceYesThreshold < targetNoThreshold)
    (hSource : gCost ≤ sourceYesThreshold) :
    ¬ TargetNo gCost targetNoThreshold := by
  unfold TargetNo
  linarith

#print axioms hard_source_forces_hard_restriction
#print axioms restriction_threshold_exponent_identity
#print axioms restriction_fraction_transfers_hard_side
#print axioms restriction_enumeration_time_exponent
#print axioms restriction_window_nonempty_iff
#print axioms ignored_variable_promise_collision
#print axioms extension_restriction_cost_equality
#print axioms promise_collision_interval_empty_of_separated_thresholds

end PNPMCSPRestrictionTransformerFirewall
