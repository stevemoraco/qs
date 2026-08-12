import Mathlib

namespace MillenniumCrossfeedRun21

/--
If a translated interval of width `H` starts between two consecutive grid points
`n*δ` and `(n+1)*δ`, with `δ ≤ H`, then every point of the translated
interval lies in one of the two adjacent grid-aligned intervals of width `H`.
This is the order-theoretic core behind the Run21 RH lattice-window reduction.
-/
theorem shifted_window_two_grid_cover
    {H δ T n t : ℝ}
    (hδ : 0 < δ)
    (hδH : δ ≤ H)
    (hnlo : n * δ ≤ T)
    (hnhi : T < (n + 1) * δ)
    (htlo : T ≤ t)
    (hthi : t ≤ T + H) :
    (n * δ ≤ t ∧ t ≤ n * δ + H) ∨
      ((n + 1) * δ ≤ t ∧ t ≤ (n + 1) * δ + H) := by
  by_cases hfirst : t ≤ n * δ + H
  · left
    constructor
    · linarith
    · exact hfirst
  · right
    have hgt : n * δ + H < t := lt_of_not_ge hfirst
    constructor
    · nlinarith
    · linarith

/--
A finite global budget contradicts an unbounded sequence of cumulative lower
prices.  No uniform positive per-event floor is required: non-summability of
the proved lower prices is the exact abstract endpoint.
-/
theorem unbounded_partial_prices_contradict_budget
    {cost : ℕ → ℝ} {E : ℝ}
    (hbudget : ∀ N : ℕ, ∑ j in Finset.range N, cost j ≤ E)
    (hunbounded : ∀ B : ℝ, ∃ N : ℕ, B < ∑ j in Finset.range N, cost j) :
    False := by
  rcases hunbounded E with ⟨N, hN⟩
  exact (not_lt_of_ge (hbudget N)) hN

/--
For an antitone positive-master candidate, every real-time value between two
adjacent sample times is squeezed by those two samples.  This is the finite
order core used only as a downstream Yang--Mills discretization observation.
-/
theorem monotone_unit_window_squeeze
    {M : ℝ → ℝ}
    (hmono : Antitone M)
    {t n : ℝ}
    (hnt : n ≤ t)
    (htn : t ≤ n + 1) :
    M (n + 1) ≤ M t ∧ M t ≤ M n := by
  constructor
  · exact hmono htn
  · exact hmono hnt

#print axioms shifted_window_two_grid_cover
#print axioms unbounded_partial_prices_contradict_budget
#print axioms monotone_unit_window_squeeze

end MillenniumCrossfeedRun21
