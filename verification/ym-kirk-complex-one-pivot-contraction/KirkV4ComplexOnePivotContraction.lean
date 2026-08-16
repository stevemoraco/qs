import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 complex one-pivot contraction margin

Finite scalar bridge for the compact Haar-pivot repair.

If the real centered one-pivot contraction is `theta < 1` and a complex optical
perturbation changes its operator norm by at most `C * r`, then the strict
margin survives on any tube satisfying `2 * C * r <= 1 - theta`.

This is only the scalar margin arithmetic after a source-level operator
Lipschitz/trace-norm estimate has been supplied. It does not prove Kirk's
complex optical operator estimate, the rooted complex denominator theorem,
Theorem 6.43, Osterwalder--Schrader reconstruction, the Yang--Mills mass gap,
or a Clay theorem.
-/

theorem complex_one_pivot_midpoint_bound
    (theta C r : ℝ)
    (hsmall : 2 * C * r ≤ 1 - theta) :
    theta + C * r ≤ (1 + theta) / 2 := by
  linarith

theorem complex_one_pivot_contraction
    (theta C r bound : ℝ)
    (htheta : theta < 1)
    (hbound : bound ≤ theta + C * r)
    (hsmall : 2 * C * r ≤ 1 - theta) :
    bound < 1 := by
  have hmid : theta + C * r ≤ (1 + theta) / 2 :=
    complex_one_pivot_midpoint_bound theta C r hsmall
  linarith

theorem complex_one_pivot_explicit_margin
    (theta C r bound : ℝ)
    (hbound : bound ≤ theta + C * r)
    (hsmall : 2 * C * r ≤ 1 - theta) :
    bound ≤ (1 + theta) / 2 := by
  exact hbound.trans (complex_one_pivot_midpoint_bound theta C r hsmall)

#print axioms complex_one_pivot_midpoint_bound
#print axioms complex_one_pivot_contraction
#print axioms complex_one_pivot_explicit_margin

end Millennium.YangMills
