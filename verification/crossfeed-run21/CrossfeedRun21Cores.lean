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
Any monotone subadditive nonnegative-mass surrogate on real sets inherits the
two-tile bound.  A local integral of a nonnegative energy density is the target
paper-level instantiation in the RH lane.
-/
theorem two_tile_mass_bound
    {H δ T n : ℝ}
    (mass : Set ℝ → ℝ)
    (hmono : Monotone mass)
    (hsub : ∀ A B : Set ℝ, mass (A ∪ B) ≤ mass A + mass B)
    (hδH : δ ≤ H)
    (hnlo : n * δ ≤ T)
    (hnhi : T < (n + 1) * δ) :
    mass (Set.Icc T (T + H)) ≤
      mass (Set.Icc (n * δ) (n * δ + H)) +
        mass (Set.Icc ((n + 1) * δ) ((n + 1) * δ + H)) := by
  have hsubset :
      Set.Icc T (T + H) ⊆
        Set.Icc (n * δ) (n * δ + H) ∪
          Set.Icc ((n + 1) * δ) ((n + 1) * δ + H) := by
    intro t ht
    rcases shifted_window_two_grid_cover hδH hnlo hnhi ht.1 ht.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact le_trans (hmono hsubset) (hsub _ _)

/--
A finite global budget contradicts an unbounded sequence of cumulative lower
prices. No uniform positive per-event floor is required: unbounded cumulative
proved lower prices are the exact abstract endpoint.
-/
theorem unbounded_partial_prices_contradict_budget
    {cost : ℕ → ℝ} {E : ℝ}
    (hbudget : ∀ N : ℕ, Finset.sum (Finset.range N) cost ≤ E)
    (hunbounded : ∀ B : ℝ, ∃ N : ℕ, B < Finset.sum (Finset.range N) cost) :
    False := by
  rcases hunbounded E with ⟨N, hN⟩
  exact (not_lt_of_ge (hbudget N)) hN

/--
For an antitone positive-master candidate, every real-time value between two
adjacent sample times is squeezed by those two samples. This is the finite
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
#print axioms two_tile_mass_bound
#print axioms unbounded_partial_prices_contradict_budget
#print axioms monotone_unit_window_squeeze

end MillenniumCrossfeedRun21
