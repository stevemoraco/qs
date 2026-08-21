import Mathlib

namespace Millennium.BSD

/-!
# Neumann–Setzer distinct-semiprime two-state core

Finite arithmetic only.  The arithmetic application has nonnegative integers
`r`, `d`, `t` denoting Mordell–Weil rank, divisible 2-primary Sha corank,
and finite reduced 2-primary 2-torsion dimension.  The source inputs give
`r + d + t ≤ 1` and oddness of `r + d`.

This file does not formalize elliptic curves, Selmer groups, Sha, parity, BSD,
or any Millennium endpoint.
-/

/-- A nonnegative three-term budget of at most one, together with oddness of
the first two terms, has exactly two possible states. -/
theorem semiprime_two_state_dichotomy
    (r d t : ℕ)
    (hbudget : r + d + t ≤ 1)
    (hodd : Odd (r + d)) :
    (r = 1 ∧ d = 0 ∧ t = 0) ∨
      (r = 0 ∧ d = 1 ∧ t = 0) := by
  rcases hodd with ⟨k, hk⟩
  omega

/-- In either state the finite reduced 2-primary contribution vanishes. -/
theorem semiprime_finite_reduced_part_vanishes
    (r d t : ℕ)
    (hbudget : r + d + t ≤ 1)
    (hodd : Odd (r + d)) :
    t = 0 := by
  rcases semiprime_two_state_dichotomy r d t hbudget hodd with h | h
  · exact h.2.2
  · exact h.2.2

/-- If the divisible corank is zero, the only remaining state has rank one. -/
theorem semiprime_rank_one_of_divisible_corank_zero
    (r d t : ℕ)
    (hbudget : r + d + t ≤ 1)
    (hodd : Odd (r + d))
    (hd : d = 0) :
    r = 1 ∧ t = 0 := by
  rcases semiprime_two_state_dichotomy r d t hbudget hodd with h | h
  · exact ⟨h.1, h.2.2⟩
  · omega

/-- If the Mordell–Weil rank is zero, the remaining state has one divisible
2-primary corank and no finite reduced 2-primary contribution. -/
theorem semiprime_divisible_state_of_rank_zero
    (r d t : ℕ)
    (hbudget : r + d + t ≤ 1)
    (hodd : Odd (r + d))
    (hr : r = 0) :
    d = 1 ∧ t = 0 := by
  rcases semiprime_two_state_dichotomy r d t hbudget hodd with h | h
  · omega
  · exact ⟨h.2.1, h.2.2⟩

#print axioms semiprime_two_state_dichotomy
#print axioms semiprime_finite_reduced_part_vanishes
#print axioms semiprime_rank_one_of_divisible_corank_zero
#print axioms semiprime_divisible_state_of_rank_zero

end Millennium.BSD
