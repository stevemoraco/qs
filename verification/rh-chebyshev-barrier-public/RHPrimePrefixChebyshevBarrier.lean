import Mathlib

namespace RHPrimePrefixChebyshevBarrier

/-- Root-coordinate algebra behind the Chebyshev barrier.

Interpret `a = sqrt(theta(q))`, `b = sqrt(theta(q^-))`,
`s = sqrt(q)`, and `w = log q`. If `theta(q) <= q`, then `a <= s`.
The prime-prefix increment is `2(a-b)-w/s`; under
`w = a^2-b^2` it is strictly positive. -/
theorem positive_increment_of_chebyshev_barrier
    {a b s w : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hba : b < a)
    (has : a ≤ s)
    (hw : w = a ^ 2 - b ^ 2) :
    0 < 2 * (a - b) - w / s := by
  have hs : 0 < s := lt_of_lt_of_le ha has
  have hab : 0 < a - b := sub_pos.mpr hba
  have hsecond : 0 < 2 * s - a - b := by
    nlinarith
  rw [hw]
  have hid :
      2 * (a - b) - (a ^ 2 - b ^ 2) / s =
        ((a - b) * (2 * s - a - b)) / s := by
    field_simp [ne_of_gt hs]
    ring
  rw [hid]
  exact div_pos (mul_pos hab hsecond) hs

/-- The exact square reserve left after replacing the denominator `s` by the
larger endpoint `a`. -/
theorem endpoint_square_reserve_identity
    {a b : ℝ}
    (ha : a ≠ 0) :
    2 * (a - b) - (a ^ 2 - b ^ 2) / a =
      (a - b) ^ 2 / a := by
  field_simp [ha]
  ring

/-- A positive reserve remains positive after one positive arrival. -/
theorem positive_reserve_after_positive_arrival
    {F delta Fnext : ℝ}
    (hF : 0 < F)
    (hdelta : 0 < delta)
    (hnext : Fnext = F + delta) :
    0 < Fnext := by
  rw [hnext]
  exact add_pos hF hdelta

/-- A finite list of positive arrivals preserves a positive initial reserve. -/
theorem positive_reserve_after_finite_arrivals
    {F0 : ℝ}
    {deltas : List ℝ}
    (hF0 : 0 < F0)
    (hdeltas : ∀ d ∈ deltas, 0 < d) :
    0 < F0 + deltas.sum := by
  have hsum : 0 ≤ deltas.sum := by
    exact List.sum_nonneg fun d hd => le_of_lt (hdeltas d hd)
  exact add_pos_of_pos_of_nonneg hF0 hsum

/-- Exact rational surplus in the elementary lower bound
`log 6 > 16/9` used by the human proof of `F(3)>0`. -/
theorem base_log_budget_rational_surplus :
    (56 : ℚ) / 81 + 263 / 240 - 16 / 9 = 61 / 6480 := by
  norm_num

/-- The rational surplus is strictly positive. -/
theorem base_log_budget_rational_positive :
    (0 : ℚ) < (56 : ℚ) / 81 + 263 / 240 - 16 / 9 := by
  rw [base_log_budget_rational_surplus]
  norm_num

#print axioms positive_increment_of_chebyshev_barrier
#print axioms endpoint_square_reserve_identity
#print axioms positive_reserve_after_positive_arrival
#print axioms positive_reserve_after_finite_arrivals
#print axioms base_log_budget_rational_surplus
#print axioms base_log_budget_rational_positive

end RHPrimePrefixChebyshevBarrier
