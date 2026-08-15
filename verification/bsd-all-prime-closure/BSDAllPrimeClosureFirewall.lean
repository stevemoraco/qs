import Mathlib

/-!
# BSD lane: all-prime closure finite core

This file formalizes a finite arithmetic shadow of the global exactness step in
the strong Birch--Swinnerton-Dyer leading-coefficient formula.

If a positive rational discrepancy has been reduced to coprime numerator and
denominator and every prime valuation is already known to vanish, then neither
the numerator nor denominator can have a prime divisor. The only natural
number with no prime divisor is `1`; hence the reduced discrepancy is exactly
`1`.

Here we formalize only the load-bearing finite implication "no prime support
forces 1". We do **not** formalize elliptic curves, valuations, p-adic BSD,
periods, regulators, or the Birch--Swinnerton-Dyer conjecture.
-/

namespace BSDAllPrimeClosureFirewall

theorem no_prime_divisor_forces_one
    {n : ℕ}
    (hnone : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ n) :
    n = 1 := by
  by_contra hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
  exact (hnone p hp) hpd

theorem numerator_denominator_prime_support_closed
    {a b : ℕ}
    (ha : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ a)
    (hb : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ b) :
    a = 1 ∧ b = 1 := by
  exact ⟨no_prime_divisor_forces_one ha, no_prime_divisor_forces_one hb⟩

theorem all_prime_closure_cross_product
    {a b : ℕ}
    (ha : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ a)
    (hb : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ b) :
    a = b := by
  rcases numerator_denominator_prime_support_closed ha hb with ⟨rfl, rfl⟩
  rfl

theorem odd_prime_control_does_not_force_one :
    (∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ p ∣ 2) ∧ (2 : ℕ) ≠ 1 := by
  constructor
  · intro p hp hp2 hdiv
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hp_ge : 2 ≤ p := hp.two_le
    have : p = 2 := Nat.le_antisymm hp_le hp_ge
    exact hp2 this
  · norm_num

#print axioms no_prime_divisor_forces_one
#print axioms numerator_denominator_prime_support_closed
#print axioms all_prime_closure_cross_product
#print axioms odd_prime_control_does_not_force_one

end BSDAllPrimeClosureFirewall
