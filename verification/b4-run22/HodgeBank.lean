import Mathlib

/-!
# Hodge lane: selected-count and scalar-annihilator arithmetic

This file isolates two elementary identities used in a comparison with a
global secant construction.

For every odd integer `d ≥ 3`, the selected count
`(d+9)(2d-1)` is strictly positive.

Over a commutative ring, the scalar relation `t²=-d` makes
`d*b+t²*b` vanish. The same identity applies independently to
coefficients labelled by the `+t` and `-t` exponent branches.

This is only arithmetic and scalar algebra. It does not formalize the
geometric selected set, exponentials, characteristic classes, Markman's
global theorem, semiregularity, or the Hodge conjecture.
-/

namespace Millennium.Hodge.MarkmanScalarCount

/-- The selected-count polynomial is positive for every odd `d ≥ 3`.
Oddness is retained to match the intended application, although the
inequality itself only needs the lower bound. -/
theorem selected_count_positive {d : ℤ}
    (hd : 3 ≤ d) (hodd : Odd d) :
    0 < (d + 9) * (2 * d - 1) := by
  have hleft : 0 < d + 9 := by omega
  have hright : 0 < 2 * d - 1 := by omega
  exact mul_pos hleft hright

/-- Abstract scalar annihilator identity. -/
theorem secant_scalar_annihilator
    {S : Type*} [CommRing S] {d t b : S}
    (ht : t ^ 2 = -d) :
    d * b + t ^ 2 * b = 0 := by
  rw [ht]
  ring

/-- Both formal exponent branches, labelled by `+t` and `-t`, obey
the same coefficient-level annihilator identity. -/
theorem secant_two_branch_annihilator
    {S : Type*} [CommRing S] {d t bPlus bMinus : S}
    (ht : t ^ 2 = -d) :
    (d * bPlus + t ^ 2 * bPlus = 0) ∧
    (d * bMinus + (-t) ^ 2 * bMinus = 0) := by
  constructor
  · exact secant_scalar_annihilator ht
  · have hneg : (-t) ^ 2 = -d := by
      rw [sq_neg, ht]
    exact secant_scalar_annihilator hneg

#print axioms selected_count_positive
#print axioms secant_scalar_annihilator
#print axioms secant_two_branch_annihilator

end Millennium.Hodge.MarkmanScalarCount
