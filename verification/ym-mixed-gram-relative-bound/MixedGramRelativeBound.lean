import Mathlib

namespace Millennium.YangMills

/-!
# Mixed-Gram absolute form bound

A positive semidefinite two-cell Gram form does not make its off-diagonal
mask positive, but evaluating the full form at `(x,y)` and `(x,-y)` gives
an exact absolute domination of the mixed term by the same-cell diagonal
energy.

This is finite real algebra only. It does not formalize the Yang--Mills
operator instantiation.
-/

/-- If a real two-variable quadratic form is nonnegative everywhere, then
its mixed/off-diagonal term is absolutely bounded by the diagonal part. -/
theorem two_cell_mixed_absolute_bound
    (a b c : ℝ)
    (hpsd : ∀ x y : ℝ, 0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2)
    (x y : ℝ) :
    |2 * b * x * y| ≤ a * x ^ 2 + c * y ^ 2 := by
  have hplus := hpsd x y
  have hminus := hpsd x (-y)
  rw [abs_le]
  constructor <;> nlinarith

/-- Upper half of the same mixed-form domination. -/
theorem two_cell_mixed_upper
    (a b c : ℝ)
    (hpsd : ∀ x y : ℝ, 0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2)
    (x y : ℝ) :
    2 * b * x * y ≤ a * x ^ 2 + c * y ^ 2 := by
  have h := two_cell_mixed_absolute_bound a b c hpsd x y
  exact le_trans (le_abs_self (2 * b * x * y)) h

/-- Lower half of the same mixed-form domination. -/
theorem two_cell_mixed_lower
    (a b c : ℝ)
    (hpsd : ∀ x y : ℝ, 0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2)
    (x y : ℝ) :
    -(a * x ^ 2 + c * y ^ 2) ≤ 2 * b * x * y := by
  have h := two_cell_mixed_absolute_bound a b c hpsd x y
  have habs : -(a * x ^ 2 + c * y ^ 2) ≤ -|2 * b * x * y| := by
    linarith
  exact le_trans habs (neg_abs_le (2 * b * x * y))

/-- The constant one in the two-cell absolute bound is sharp: the rank-one
Gram matrix `[[1,1],[1,1]]` attains equality at `(1,1)`. -/
theorem two_cell_mixed_bound_sharp :
    |(2 : ℝ) * 1 * 1| = (1 : ℝ) * 1 ^ 2 + (1 : ℝ) * 1 ^ 2 := by
  norm_num

#print axioms two_cell_mixed_absolute_bound
#print axioms two_cell_mixed_upper
#print axioms two_cell_mixed_lower
#print axioms two_cell_mixed_bound_sharp

end Millennium.YangMills
