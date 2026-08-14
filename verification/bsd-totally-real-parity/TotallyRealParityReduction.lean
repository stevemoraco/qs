import Mathlib

/-!
Finite logical core for the totally-real p=2 converse reduction.

Arithmetic application: Green--Maistret prove p-parity for elliptic curves over
totally real fields. Therefore a p-infinity Selmer corank-one instance has odd
analytic rank. To conclude analytic rank one it is enough to exclude analytic
rank at least three.

This file proves only that natural-number parity squeeze. It does not formalize
Selmer groups, L-functions, the Green--Maistret theorem, quadratic base change,
or BSD.
-/

namespace Millennium.BSD

/-- An odd natural number strictly below three is one. -/
theorem odd_lt_three_eq_one
    (a : ℕ)
    (hodd : a % 2 = 1)
    (hlt : a < 3) :
    a = 1 := by
  omega

/-- If Selmer and analytic ranks have the same parity and the Selmer rank is
one, analytic rank one is equivalent to the weaker analytic upper bound `< 3`.-/
theorem parity_reduces_rank_one_converse
    (sel an : ℕ)
    (hsel : sel = 1)
    (hparity : an % 2 = sel % 2) :
    (an = 1 ↔ an < 3) := by
  constructor
  · intro h
    omega
  · intro hlt
    have hodd : an % 2 = 1 := by
      simpa [hsel] using hparity
    exact odd_lt_three_eq_one an hodd hlt

/-- Equivalent obstruction form: under rank-one Selmer parity, failure of
analytic rank one forces analytic rank at least three. -/
theorem parity_rank_one_failure_forces_three
    (sel an : ℕ)
    (hsel : sel = 1)
    (hparity : an % 2 = sel % 2)
    (hne : an ≠ 1) :
    3 ≤ an := by
  by_contra h
  have hlt : an < 3 := Nat.lt_of_not_ge h
  exact hne ((parity_reduces_rank_one_converse sel an hsel hparity).2 hlt)

#print axioms odd_lt_three_eq_one
#print axioms parity_reduces_rank_one_converse
#print axioms parity_rank_one_failure_forces_three

end Millennium.BSD
