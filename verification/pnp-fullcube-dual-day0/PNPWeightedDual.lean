import Mathlib

open scoped BigOperators

namespace PNPFullCubeDual

/--
Finite weighted-cover duality.

If every point has error probability at most `ε`, nonnegative weights have
expected covered mass at least one only when their total mass is at least
`1 / ε`.

In the full-cube parity obstruction, substituting
`ε = (3 * q - 2) / q ^ 2` gives the fractional-transversal lower bound
`q ^ 2 / (3 * q - 2)`.
-/
theorem weighted_cover_mass_lower_bound
    {X : Type*} [Fintype X]
    (weight errorProb : X → ℝ) (ε : ℝ)
    (weight_nonneg : ∀ x, 0 ≤ weight x)
    (pointwise_error : ∀ x, errorProb x ≤ ε)
    (covered_mass : 1 ≤ ∑ x, weight x * errorProb x)
    (epsilon_pos : 0 < ε) :
    1 / ε ≤ ∑ x, weight x := by
  apply (div_le_iff₀ epsilon_pos).2
  calc
    1 ≤ ∑ x, weight x * errorProb x := covered_mass
    _ ≤ ∑ x, weight x * ε := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact mul_le_mul_of_nonneg_left (pointwise_error x) (weight_nonneg x)
    _ = (∑ x, weight x) * ε := by
      rw [Finset.sum_mul]

end PNPFullCubeDual
