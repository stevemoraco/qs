import Mathlib

/-!
Lean-ready finite core for the BSD finite-prime + square-class obstruction.

This file proves only the valuation-free combinatorial/arithmetic kernel:
for any finite set of primes there is a prime outside it whose rational square
is positive and nontrivial.  The p-adic valuation corollary can then be layered
on using the valuation API.

No BSD statement is asserted here.
-/

namespace BSDFinitePrimeCore

/-- Every finite set of naturals misses some prime. -/
theorem exists_prime_not_mem_finset (S : Finset ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∉ S := by
  by_cases hS : S.Nonempty
  · obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (S.max' hS + 1)
    refine ⟨q, hprime, ?_⟩
    intro hmem
    have hle : q ≤ S.max' hS := S.le_max' q hmem
    omega
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes 2
    refine ⟨q, hprime, ?_⟩
    simp [hempty]

/--
For every finite prime set there is a positive nontrivial rational square
built from a prime outside that set.
-/
theorem finite_prime_square_ambiguity_core (S : Finset ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∉ S ∧
      (0 : ℚ) < (q : ℚ) ^ 2 ∧ (q : ℚ) ^ 2 ≠ 1 := by
  obtain ⟨q, hprime, hqS⟩ := exists_prime_not_mem_finset S
  refine ⟨q, hprime, hqS, ?_, ?_⟩
  · have hqpos : (0 : ℚ) < q := by
      exact_mod_cast hprime.pos
    positivity
  · have hq2 : (2 : ℚ) ≤ q := by
      exact_mod_cast hprime.two_le
    intro heq
    have hgt : (1 : ℚ) < (q : ℚ) ^ 2 := by
      nlinarith
    linarith

end BSDFinitePrimeCore
