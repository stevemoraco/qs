import Mathlib

/-!
# Round 205 RH trace-to-rank floor

This file formalizes only finite trace bookkeeping. It does not formalize
trace-class operators, the Suzuki multiplier, the Weil quadratic form, zeta,
or the Riemann hypothesis.
-/

open scoped BigOperators

namespace Millennium
namespace Round205RH

/-- If a rank-`N` compression captures at most `M` per mode, its captured trace
is at most `N*M`. -/
theorem captured_trace_le_rank_mul_opnorm
    {ι : Type*}
    (s : Finset ι) (captured : ι → ℝ) (M : ℝ)
    (hcap : ∀ i ∈ s, captured i ≤ M) :
    (∑ i ∈ s, captured i) ≤ (s.card : ℝ) * M := by
  calc
    (∑ i ∈ s, captured i) ≤ ∑ _i ∈ s, M := by
      exact Finset.sum_le_sum fun i hi => hcap i hi
    _ = (s.card : ℝ) * M := by simp

/-- Total trace minus the maximal rank-`N` captured budget is a lower bound
for the uncaptured trace tail. -/
theorem trace_tail_rank_floor
    {ι : Type*}
    (s : Finset ι) (captured : ι → ℝ)
    (total tail M : ℝ)
    (hdecomp : total = (∑ i ∈ s, captured i) + tail)
    (hcap : ∀ i ∈ s, captured i ≤ M) :
    total - (s.card : ℝ) * M ≤ tail := by
  have hsum := captured_trace_le_rank_mul_opnorm s captured M hcap
  linarith

/-- If the desired tail is strictly below `tau`, the rank budget must satisfy
the strict dimension inequality `total-tau < N*M`. -/
theorem small_tail_forces_rank_budget
    {ι : Type*}
    (s : Finset ι) (captured : ι → ℝ)
    (total tail M tau : ℝ)
    (hdecomp : total = (∑ i ∈ s, captured i) + tail)
    (hcap : ∀ i ∈ s, captured i ≤ M)
    (htail : tail < tau) :
    total - tau < (s.card : ℝ) * M := by
  have hfloor := trace_tail_rank_floor
    s captured total tail M hdecomp hcap
  linarith

/-- Combining a lower trace estimate `lowerTrace`, an operator bound `M`, and
a strict tail target gives the same necessary rank budget. -/
theorem lower_trace_small_tail_forces_rank_budget
    {ι : Type*}
    (s : Finset ι) (captured : ι → ℝ)
    (lowerTrace total tail M tau : ℝ)
    (hlower : lowerTrace ≤ total)
    (hdecomp : total = (∑ i ∈ s, captured i) + tail)
    (hcap : ∀ i ∈ s, captured i ≤ M)
    (htail : tail < tau) :
    lowerTrace - tau < (s.card : ℝ) * M := by
  have hrank := small_tail_forces_rank_budget
    s captured total tail M tau hdecomp hcap htail
  linarith

/-- A mere upper enclosure for a phase volume cannot be substituted for a
lower bound: every smaller nonnegative actual volume is compatible with it. -/
theorem upper_cutoff_does_not_supply_lower_volume
    (upper actual : ℝ) (hupper : 0 ≤ upper)
    (hactual : 0 ≤ actual) (hle : actual ≤ upper) :
    ∃ candidate : ℝ,
      0 ≤ candidate ∧ candidate ≤ upper ∧ candidate ≤ actual := by
  exact ⟨0, le_rfl, hupper, hactual⟩

#print axioms captured_trace_le_rank_mul_opnorm
#print axioms trace_tail_rank_floor
#print axioms small_tail_forces_rank_budget
#print axioms lower_trace_small_tail_forces_rank_budget
#print axioms upper_cutoff_does_not_supply_lower_volume

end Round205RH
end Millennium
