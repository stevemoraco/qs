import Mathlib

namespace B4Auto20Run6

/-- BANKER: for three hard-set complements with normalized density deficits
`e₀,e₁,e₂`, the union-bound lower remainder is positive whenever the total
deficit is strictly below one. This is the scalar threshold needed before a
three-algorithm common-hard-input argument can even have positive mass. -/
theorem pnp_three_deficit_budget_leaves_positive_remainder
    (e₀ e₁ e₂ : ℝ)
    (hbudget : e₀ + e₁ + e₂ < 1) :
    0 < 1 - (e₀ + e₁ + e₂) := by
  linarith

/-- CRITIC: three hard sets can each contain exactly two thirds of a three-point
universe, and every pair can overlap, while the triple intersection is empty.
Thus the two-set majority threshold from the preceding bank cannot be iterated
to a common witness for three algorithms. -/
theorem pnp_three_two_thirds_sets_pairwise_overlap_but_empty_triple :
    let H₀ : Fin 3 → Prop := fun x => x ≠ 2
    let H₁ : Fin 3 → Prop := fun x => x ≠ 0
    let H₂ : Fin 3 → Prop := fun x => x ≠ 1
    (Finset.univ.filter H₀).card = 2 ∧
    (Finset.univ.filter H₁).card = 2 ∧
    (Finset.univ.filter H₂).card = 2 ∧
    (∃ x, H₀ x ∧ H₁ x) ∧
    (∃ x, H₀ x ∧ H₂ x) ∧
    (∃ x, H₁ x ∧ H₂ x) ∧
    ¬ ∃ x, H₀ x ∧ H₁ x ∧ H₂ x := by
  decide

/-- CLEANER: the sharp union-bound-safe symmetric threshold for three sets is
strictly better than two thirds hard density for each set, equivalently each
complement deficit is strictly below one third. At that threshold the total
deficit is strictly below one. -/
theorem pnp_three_deficits_below_third_sum_below_one
    (e₀ e₁ e₂ : ℝ)
    (h₀ : e₀ < (1 : ℝ) / 3)
    (h₁ : e₁ < (1 : ℝ) / 3)
    (h₂ : e₂ < (1 : ℝ) / 3) :
    e₀ + e₁ + e₂ < 1 := by
  linarith

#print axioms B4Auto20Run6.pnp_three_deficit_budget_leaves_positive_remainder
#print axioms B4Auto20Run6.pnp_three_two_thirds_sets_pairwise_overlap_but_empty_triple
#print axioms B4Auto20Run6.pnp_three_deficits_below_third_sum_below_one

end B4Auto20Run6
