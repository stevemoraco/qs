import Mathlib

namespace B4Auto20Run5

/-- BANKER: if `N` bad events each consume at least a uniform dissipation amount
`δ > 0`, and the total available dissipation is at most `E`, then the event count
obeys the quantitative budget `N ≤ E/δ`. This is the scalar counting core behind
any Navier–Stokes argument that rules out infinitely many concentration events
by charging each event a fixed amount of a finite energy budget. -/
theorem ns_uniform_event_cost_bounds_event_count
    (N : ℕ) (δ E : ℝ) (hδ : 0 < δ)
    (hbudget : (N : ℝ) * δ ≤ E) :
    (N : ℝ) ≤ E / δ := by
  exact (le_div_iff₀ hδ).2 hbudget

/-- CRITIC: if the event cost is allowed to vanish, the counting mechanism gives
no control at all: every finite event count is compatible with zero total cost.
Thus positivity of dissipation without a uniform positive lower bound is not
sufficient for this particular exclusion mechanism. -/
theorem ns_zero_event_cost_allows_arbitrary_finite_count
    (N : ℕ) :
    (N : ℝ) * 0 ≤ 1 := by
  norm_num

/-- CLEANER: a strict event-count violation certifies that the assumed uniform
per-event dissipation price cannot simultaneously hold with the global budget.
This packages the exact contradiction a recurrence/exclusion proof must reach. -/
theorem ns_too_many_events_contradict_uniform_cost
    (N : ℕ) (δ E : ℝ) (hδ : 0 < δ)
    (hmany : E / δ < (N : ℝ)) :
    ¬ (N : ℝ) * δ ≤ E := by
  intro hbudget
  have hcount := ns_uniform_event_cost_bounds_event_count N δ E hδ hbudget
  linarith

#print axioms B4Auto20Run5.ns_uniform_event_cost_bounds_event_count
#print axioms B4Auto20Run5.ns_zero_event_cost_allows_arbitrary_finite_count
#print axioms B4Auto20Run5.ns_too_many_events_contradict_uniform_cost

end B4Auto20Run5
