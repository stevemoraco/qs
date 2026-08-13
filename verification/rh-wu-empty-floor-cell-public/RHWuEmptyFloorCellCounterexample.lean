import Mathlib

namespace RHWuEmptyFloorCellCounterexample

/-- For N=3 and every admissible k in {1,2,3}, floor(3/k) is never 2.
This is the finite counterexample to the universal nonempty-floor-cell premise
used in Wu 2026 v4, Lemma 9. -/
theorem floor_three_ne_two
    (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    3 / k ≠ 2 := by
  interval_cases k <;> norm_num at *

/-- The claimed positive lower bound for the N=3,m=2 floor cell reduces to
`0 ≥ 1/4`, which is false. -/
theorem zero_not_ge_quarter :
    ¬ ((0 : ℚ) ≥ 1 / 4) := by
  norm_num

/-- Abstractly, if a finite fiber is empty then its nonnegative weight sum is
zero, so it cannot satisfy a strictly positive lower bound. -/
theorem empty_fiber_cannot_fund_positive
    {α : Type*} [DecidableEq α]
    (w : α → ℚ) (c : ℚ) (hc : 0 < c) :
    ¬ (∑ x ∈ (∅ : Finset α), w x) ≥ c := by
  simp [hc.not_le]

#print axioms floor_three_ne_two
#print axioms zero_not_ge_quarter
#print axioms empty_fiber_cannot_fund_positive

end RHWuEmptyFloorCellCounterexample
