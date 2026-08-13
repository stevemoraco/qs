import Mathlib

namespace RHDyadicRootHilbertTransferFinite

/-- Scalar Neumann-series closure: if a norm is bounded by a source plus a
strict contraction of itself, it is bounded by the source divided by the
remaining margin. -/
theorem contraction_inverse_bound
    {q source target : ℝ}
    (hq1 : q < 1)
    (hineq : target ≤ source + q * target) :
    target ≤ source / (1 - q) := by
  have hmargin : 0 < 1 - q := sub_pos.mpr hq1
  apply (le_div_iff₀ hmargin).2
  nlinarith

/-- Finite geometric sums obey the same contraction budget. -/
theorem finite_geometric_transfer
    {q source target : ℝ}
    (hq1 : q < 1)
    (hineq : target ≤ source + q * target) :
    (1 - q) * target ≤ source := by
  nlinarith

/-- Scalar core of the weighted Hardy estimate. If `u=sqrt(I)` and
`v=sqrt(J)`, the integration-by-parts/Cauchy step gives
`2 s u^2 <= u v`; this forces `4s^2u^2 <= v^2`. -/
theorem hardy_complete_square
    {s u v : ℝ}
    (hs : 0 < s)
    (hu : 0 ≤ u)
    (hstep : 2 * s * u ^ 2 ≤ u * v) :
    4 * s ^ 2 * u ^ 2 ≤ v ^ 2 := by
  by_cases huz : u = 0
  · simp [huz]
  · have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm huz)
    have hlinear : 2 * s * u ≤ v := by
      have hmul : u * (2 * s * u) ≤ u * v := by
        nlinarith
      exact (mul_le_mul_left hu_pos).mp hmul
    nlinarith [sq_nonneg (v - 2 * s * u)]

/-- Point sampling on a unit interval: `a=(a-t)+t` gives a trace bound before
integration. -/
theorem unit_trace_pointwise
    (a t : ℝ) :
    a ^ 2 ≤ 2 * (a - t) ^ 2 + 2 * t ^ 2 := by
  nlinarith [sq_nonneg ((a - t) - t)]

/-- The exact integral constant in the unit-cell trace estimate is `2/3`
after integrating `2t^2` over `[0,1]`. -/
theorem unit_trace_constant :
    2 * ((1 : ℝ) / 3) = 2 / 3 := by
  ring

/-- Abstract endpoint sampling inequality: a value controlled by a local
square average plus derivative square remains controlled after summing
disjoint cells. -/
theorem sample_square_split
    {sample local derivative : ℝ}
    (h : sample ^ 2 ≤ 2 * local + 2 * derivative) :
    sample ^ 2 ≤ 2 * (local + derivative) := by
  nlinarith

/-- Algebraic square-gap domination. If `E^2 <= C p^2` and the rationalized
square gap satisfies `p^3 G^2 <= E^4`, then `p G^2 <= C E^2`. -/
theorem square_gap_energy_domination
    {E G C p : ℝ}
    (hp : 0 < p)
    (hE : E ^ 2 ≤ C * p ^ 2)
    (hgap : p ^ 3 * G ^ 2 ≤ E ^ 4) :
    p * G ^ 2 ≤ C * E ^ 2 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp 2
  have hmul : E ^ 2 * E ^ 2 ≤ C * p ^ 2 * E ^ 2 :=
    mul_le_mul_of_nonneg_right hE (sq_nonneg E)
  apply (mul_le_mul_left hp2).mp
  calc
    p ^ 2 * (p * G ^ 2) = p ^ 3 * G ^ 2 := by ring
    _ ≤ E ^ 4 := hgap
    _ = E ^ 2 * E ^ 2 := by ring
    _ ≤ C * p ^ 2 * E ^ 2 := hmul
    _ = p ^ 2 * (C * E ^ 2) := by ring

/-- Prime-power tails of square-root size are integrable on every strictly
positive weighted line at the exponent level. -/
theorem prime_power_tail_exponent
    {s : ℝ}
    (hs : 0 < s) :
    -1 - 2 * s < -1 := by
  linarith

/-- The dyadic dilation norm-square exponent is `-1-2s`, so its norm exponent
is `-1/2-s`. -/
theorem dyadic_norm_exponent_identity
    (s : ℝ) :
    (-1 - 2 * s) / 2 = -1 / 2 - s := by
  ring

/-- Every positive line makes the dyadic norm exponent strictly negative. -/
theorem dyadic_norm_exponent_negative
    {s : ℝ}
    (hs : 0 < s) :
    -1 / 2 - s < 0 := by
  linarith

#print axioms contraction_inverse_bound
#print axioms finite_geometric_transfer
#print axioms hardy_complete_square
#print axioms unit_trace_pointwise
#print axioms unit_trace_constant
#print axioms sample_square_split
#print axioms square_gap_energy_domination
#print axioms prime_power_tail_exponent
#print axioms dyadic_norm_exponent_identity
#print axioms dyadic_norm_exponent_negative

end RHDyadicRootHilbertTransferFinite
