import Mathlib

namespace RHPositiveExcessL2Block

/--
Finite scalar core of the dyadic Cauchy--Schwarz step.

`L^2 <= X Q` abstracts Cauchy--Schwarz on a block of length `X`, while
`Q <= C X^2` abstracts the dyadic mean-square theorem.  The conclusion is
exactly the square of the critical `X^(3/2)` positive-area scale.
-/
theorem block_l2_to_l1_square
    (L Q X C : ℝ)
    (hX : 0 ≤ X)
    (hCS : L ^ 2 ≤ X * Q)
    (hQ : Q ≤ C * X ^ 2) :
    L ^ 2 ≤ C * X ^ 3 := by
  calc
    L ^ 2 ≤ X * Q := hCS
    _ ≤ X * (C * X ^ 2) := mul_le_mul_of_nonneg_left hQ hX
    _ = C * X ^ 3 := by ring

/-- A strict mean-square margin gives a strict critical-scale margin. -/
theorem block_l2_to_l1_square_strict
    (L Q X C : ℝ)
    (hX : 0 < X)
    (hCS : L ^ 2 ≤ X * Q)
    (hQ : Q < C * X ^ 2) :
    L ^ 2 < C * X ^ 3 := by
  calc
    L ^ 2 ≤ X * Q := hCS
    _ < X * (C * X ^ 2) := mul_lt_mul_of_pos_left hQ hX
    _ = C * X ^ 3 := by ring

/--
The critical square-root model saturates the scale identity: a dyadic
mean-square budget of order `X^2` permits a squared positive-area budget of
order `X^3`.  No logarithmic gain is present in this finite algebra alone.
-/
theorem critical_scale_saturates (X : ℝ) :
    X ^ 3 = X * X ^ 2 := by
  ring

#print axioms RHPositiveExcessL2Block.block_l2_to_l1_square
#print axioms RHPositiveExcessL2Block.block_l2_to_l1_square_strict
#print axioms RHPositiveExcessL2Block.critical_scale_saturates

end RHPositiveExcessL2Block
