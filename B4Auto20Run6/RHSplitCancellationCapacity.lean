import Mathlib

namespace B4Auto20Run6

/-- BANKER: when an RH sign/budget decomposition splits the cancellative part into
`G + H`, an absolute estimate `|G| ≤ ε` and a one-sided lower bound `-β ≤ H`
can supply at most `ε + β` of negative cancellation. Therefore any budget
`D + G + H ≤ B` forces the diagonal excess `D - B` to fit inside that combined
negative capacity. -/
theorem rh_split_cancellation_capacity_must_cover_excess
    (D G H B ε β : ℝ)
    (hbudget : D + G + H ≤ B)
    (hG : |G| ≤ ε)
    (hH : -β ≤ H) :
    D - B ≤ ε + β := by
  have hGlow : -ε ≤ G := (abs_le.mp hG).1
  linarith

/-- CRITIC: if the proven negative capacity of the two cancellative pieces is
strictly smaller than the diagonal excess, the target budget is impossible.
Separate estimates cannot be treated independently; their usable cancellation
must add up to the full excess. -/
theorem rh_split_capacity_too_small_blocks_budget
    (D G H B ε β : ℝ)
    (hcapacity : ε + β < D - B)
    (hG : |G| ≤ ε)
    (hH : -β ≤ H) :
    ¬ D + G + H ≤ B := by
  intro hbudget
  have hneed := rh_split_cancellation_capacity_must_cover_excess
    D G H B ε β hbudget hG hH
  linarith

/-- CLEANER: the combined threshold is sharp. For nonnegative capacities,
choosing the two pieces at their most negative allowed values exactly closes an
excess of `ε + β`. -/
theorem rh_split_cancellation_threshold_is_sharp
    (B ε β : ℝ) (hε : 0 ≤ ε) (hβ : 0 ≤ β) :
    let D := B + ε + β
    let G := -ε
    let H := -β
    D + G + H = B ∧ |G| = ε ∧ H = -β := by
  dsimp
  constructor
  · ring
  · constructor
    · simp [abs_of_nonneg hε]
    · rfl

#print axioms B4Auto20Run6.rh_split_cancellation_capacity_must_cover_excess
#print axioms B4Auto20Run6.rh_split_capacity_too_small_blocks_budget
#print axioms B4Auto20Run6.rh_split_cancellation_threshold_is_sharp

end B4Auto20Run6
