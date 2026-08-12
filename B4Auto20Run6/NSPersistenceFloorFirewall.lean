import Mathlib

namespace B4Auto20Run6

/-- BANKER: if an amplitude `A` persists for time `τ > 0` and incurs a quadratic
charge `τ*c*A^2` with `c > 0` inside budget `E`, then its square amplitude is
bounded by `E/(τ*c)`. This is the exact scalar persistence-to-amplitude bridge. -/
theorem ns_positive_persistence_cost_bounds_amplitude_square
    (A τ c E : ℝ)
    (hτ : 0 < τ)
    (hc : 0 < c)
    (hbudget : τ * c * A ^ 2 ≤ E) :
    A ^ 2 ≤ E / (τ * c) := by
  have htc : 0 < τ * c := mul_pos hτ hc
  exact (le_div_iff₀ htc).2 (by simpa [mul_assoc] using hbudget)

/-- CRITIC: positive persistence at every amplitude does not give a uniform
amplitude bound if the persistence scale is allowed to collapse. For every
`A ≥ 1`, choosing `τ=A⁻²` keeps the quadratic charge exactly one. -/
theorem ns_inverse_square_persistence_allows_arbitrary_amplitude
    (A : ℝ) (hA : 1 ≤ A) :
    let τ : ℝ := 1 / A ^ 2
    0 < τ ∧ τ * A ^ 2 = 1 := by
  dsimp
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAne : A ≠ 0 := ne_of_gt hApos
  constructor
  · positivity
  · field_simp [hAne]

/-- CLEANER: a uniform positive persistence floor `τ₀` restores a uniform
amplitude bound. The actual persistence may be larger; the lower floor is enough
to charge every hypothetical concentration by the same minimum time scale. -/
theorem ns_uniform_persistence_floor_bounds_amplitude_square
    (A τ τ₀ c E : ℝ)
    (hτ₀ : 0 < τ₀)
    (hc : 0 < c)
    (hfloor : τ₀ ≤ τ)
    (hbudget : τ * c * A ^ 2 ≤ E) :
    A ^ 2 ≤ E / (τ₀ * c) := by
  have hc0 : 0 ≤ c := le_of_lt hc
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have htc : τ₀ * c ≤ τ * c := mul_le_mul_of_nonneg_right hfloor hc0
  have hcharge : τ₀ * c * A ^ 2 ≤ τ * c * A ^ 2 :=
    mul_le_mul_of_nonneg_right htc hA2
  have hbudget0 : τ₀ * c * A ^ 2 ≤ E := le_trans hcharge hbudget
  exact ns_positive_persistence_cost_bounds_amplitude_square A τ₀ c E hτ₀ hc hbudget0

#print axioms B4Auto20Run6.ns_positive_persistence_cost_bounds_amplitude_square
#print axioms B4Auto20Run6.ns_inverse_square_persistence_allows_arbitrary_amplitude
#print axioms B4Auto20Run6.ns_uniform_persistence_floor_bounds_amplitude_square

end B4Auto20Run6
