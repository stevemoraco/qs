import Mathlib

/-!
# BSD finite algebra: global positivity exactifies the final sign

This file formalizes the final ordered-field step used in
`GLOBAL_INTEGRAL_POSITIVITY_EXACTIFICATION_2026-08-11.md`.
It does not prove BSD.

Once equality of global fractional `ℤ`-lattices has reduced the ratio of two
rational generators to a unit of `ℤ`, the only possibilities are `+1` and
`-1`.  Positivity excludes the second possibility.
-/

namespace BSDProof
namespace GlobalPositivity

/-- Two positive rational numbers that agree up to sign are equal. -/
theorem eq_of_eq_or_eq_neg_of_pos
    {x y : ℚ}
    (hxy : x = y ∨ x = -y)
    (hx : 0 < x)
    (hy : 0 < y) :
    x = y := by
  rcases hxy with h | h
  · exact h
  · exfalso
    linarith

/-- The unit-ratio form of the same exactification step. -/
theorem eq_of_integer_unit_ratio_of_pos
    {x y : ℚ} {u : ℤ}
    (hu : u = 1 ∨ u = -1)
    (hxy : x = (u : ℚ) * y)
    (hx : 0 < x)
    (hy : 0 < y) :
    x = y := by
  rcases hu with rfl | rfl
  · simpa using hxy
  · exfalso
    norm_num at hxy
    linarith

end GlobalPositivity
end BSDProof
