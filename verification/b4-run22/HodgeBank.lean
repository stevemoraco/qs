import Mathlib

/-!
# Hodge lane: exact d=23 split moment identity

This file isolates the signed four-support presentation

`(-3,-1), (6,1), (-3,5), (1,7)`.

For the signed moment
`M_j = -3(-1)^j + 6(1)^j - 3(5)^j + 7^j`,
it proves

`(M₀,M₁,M₂,M₃,M₄) = (1,1,-23,-23,529)`.

It also checks that the four integer supports are distinct and lie in
the certified box `[-30,30]`, and that the coefficient `L¹)-size is
`3+6+3+1=13`.

This is only an exact finite K-theoretic moment certificate. It does not
prove minimality among all split presentations, a geometric realization,
semiregularity, or the Hodge conjecture.
-/

namespace Millennium.Hodge.D23SplitMoments

/-- The signed moment functional for the four-support d=23 candidate. -/
def splitMoment (j : ℕ) : ℤ :=
  (-3) * (-1) ^ j + 6 * 1 ^ j + (-3) * 5 ^ j + 1 * 7 ^ j

/-- The support `{-1,1,5,7}` is strictly ordered and lies in
`[-30,30]`. -/
theorem support_distinct_and_in_box :
    (-30 : ℤ) ≤ -1 ∧
    (-1 : ℤ) < 1 ∧
    (1 : ℤ) < 5 ∧
    (5 : ℤ) < 7 ∧
    (7 : ℤ) ≤ 30 := by
  norm_num

/-- Exact moment equations through degree four. -/
theorem splitMoment_zero_through_four :
    splitMoment 0 = 1 ∧
    splitMoment 1 = 1 ∧
    splitMoment 2 = -23 ∧
    splitMoment 3 = -23 ∧
    splitMoment 4 = 529 := by
  norm_num [splitMoment]

/-- Exact coefficient `L¹)-size of the presentation. -/
theorem coefficient_l1_eq_thirteen :
    |(-3 : ℤ)| + |(6 : ℤ)| + |(-3 : ℤ)| + |(1 : ℤ)| = 13 := by
  norm_num

#print axioms support_distinct_and_in_box
#print axioms splitMoment_zero_through_four
#print axioms coefficient_l1_eq_thirteen

end Millennium.Hodge.D23SplitMoments
