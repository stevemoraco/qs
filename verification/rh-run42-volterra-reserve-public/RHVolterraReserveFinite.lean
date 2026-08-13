import Mathlib

namespace RHVolterraReserveFinite

/-- Finite square-root-coordinate form of the concave reserve increment.
If cumulative mass moves from `v^2` to `u^2` by amount `a`, and the weighted
moment pays `a / r`, then the reserve increment factors exactly. -/
theorem concave_reserve_step
    {u v r a A₀ A₁ : ℝ}
    (hr : r ≠ 0)
    (huv : u + v ≠ 0)
    (ha : a = (u - v) * (u + v))
    (hA : A₁ = A₀ + a / r) :
    (2 * u - A₁) - (2 * v - A₀) =
      a * (2 / (u + v) - 1 / r) := by
  rw [hA, ha]
  field_simp [hr, huv]
  ring

/-- Exact endpoint decomposition: the endpoint margin is the critical
concave reserve plus a nonnegative square-over-coordinate excess. -/
theorem endpoint_excess_identity
    {p s A c : ℝ}
    (hp : p ≠ 0) :
    (p + s ^ 2 / p - c - A) =
      (2 * s - c - A) + (p - s) ^ 2 / p := by
  field_simp [hp]
  ring

/-- The first sign-transfer countermodel ledger.  The normalized Johnston
margin `1-sqrt(2)` is negative, while its causal smoothing `1-1/x` is
nonnegative for every `x ≥ 1`.  This theorem formalizes only the scalar sign
ledger, not the Volterra integral identity that produces it. -/
theorem negative_margin_positive_smoothing
    {q x : ℝ}
    (hq : q ^ 2 = 2)
    (hqpos : 0 < q)
    (hx : 1 ≤ x) :
    1 - q < 0 ∧ 0 ≤ 1 - 1 / x := by
  constructor
  · have hq1 : 1 < q := by
      nlinarith [sq_nonneg (q - 1)]
    linarith
  · have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hid : 1 - 1 / x = (x - 1) / x := by
      field_simp [hxne]
      ring
    rw [hid]
    exact div_nonneg (by linarith) (le_of_lt hxpos)

/-- Exact scalar endpoint of the converse sign-transfer countermodel.
The underlying human construction is an absolutely continuous margin that is
positive for every `x ≥ 2`, but whose causal transform at `x=11` is the value
shown here and is negative. -/
theorem positive_margin_negative_smoothing_ledger
    {q : ℝ}
    (hq : q ^ 2 = 2)
    (hqpos : 0 < q) :
    0 < (1 : ℝ) ∧
      (-71 / 11 + 25 * q / 22 : ℝ) < 0 := by
  constructor
  · norm_num
  · have hq2 : q < 2 := by
      nlinarith [sq_nonneg (q - 2)]
    nlinarith

/-- The exact integral ledger for the piecewise-linear converse countermodel. -/
theorem piecewise_integral_ledger
    {q : ℝ} :
    ((1 - q + 10) / 2 + 10 * 8 + (10 + 1) / 2 : ℝ) =
      91 - q / 2 := by
  ring

/-- Substituting the exact piecewise integral into the forward transform at
`x=11` gives the advertised negative scalar. -/
theorem piecewise_transform_ledger
    {q : ℝ} :
    (2 - (91 - q / 2) / 11 + q + (q - 2) / 11 : ℝ) =
      -71 / 11 + 25 * q / 22 := by
  ring

#print axioms concave_reserve_step
#print axioms endpoint_excess_identity
#print axioms negative_margin_positive_smoothing
#print axioms positive_margin_negative_smoothing_ledger
#print axioms piecewise_integral_ledger
#print axioms piecewise_transform_ledger

end RHVolterraReserveFinite
