import Mathlib

/-!
# BSD semistable prime certificate: finite gcd logic

This file formalizes only the finite divisibility calculation used to route
bad primes in the semistable analytic-rank-zero BSD certificate.

For a finite set of bad primes `bad`, a minimal-discriminant exponent function
`exponent`, and a candidate prime `p`, the off-diagonal gcd is the gcd of the
exponents at all bad primes other than `p`.  The main theorem proves that
`p` fails to divide this gcd exactly when there is a distinct bad prime whose
exponent is not divisible by `p`.

No elliptic curves, Galois representations, ramification theorem, Iwasawa
main conjecture, special-value formula, or BSD statement is formalized here.
-/

namespace MillenniumBSD
namespace SemistablePrimeCertificate

/-- Gcd of the local exponents away from the candidate prime `p`.
The gcd of the empty finset is `0`, matching the one-bad-prime convention. -/
def offDiagonalGcd
    (bad : Finset ℕ) (exponent : ℕ → ℕ) (p : ℕ) : ℕ :=
  (bad.erase p).gcd exponent

/-- Divisibility of the off-diagonal gcd means divisibility of every
off-diagonal exponent. -/
theorem dvd_offDiagonalGcd_iff
    (bad : Finset ℕ) (exponent : ℕ → ℕ) (p : ℕ) :
    p ∣ offDiagonalGcd bad exponent p ↔
      ∀ q, q ≠ p → q ∈ bad → p ∣ exponent q := by
  classical
  simp [offDiagonalGcd, Finset.dvd_gcd_iff]

/-- Failure of gcd divisibility is exactly the existence of one distinct
bad-prime witness whose exponent is not divisible by `p`. -/
theorem not_dvd_offDiagonalGcd_iff_exists_witness
    (bad : Finset ℕ) (exponent : ℕ → ℕ) (p : ℕ) :
    ¬ p ∣ offDiagonalGcd bad exponent p ↔
      ∃ q, q ∈ bad ∧ q ≠ p ∧ ¬ p ∣ exponent q := by
  constructor
  · intro h
    by_contra hnone
    apply h
    rw [dvd_offDiagonalGcd_iff]
    intro q hqp hqbad
    by_contra hq
    apply hnone
    exact ⟨q, hqbad, hqp, hq⟩
  · rintro ⟨q, hqbad, hqp, hq⟩ hp
    exact hq ((dvd_offDiagonalGcd_iff bad exponent p).mp hp q hqp hqbad)

/-- A concrete witness immediately forces the candidate prime not to divide
the off-diagonal gcd. -/
theorem witness_forces_not_dvd_offDiagonalGcd
    {bad : Finset ℕ} {exponent : ℕ → ℕ} {p q : ℕ}
    (hqbad : q ∈ bad) (hqp : q ≠ p) (hq : ¬ p ∣ exponent q) :
    ¬ p ∣ offDiagonalGcd bad exponent p :=
  (not_dvd_offDiagonalGcd_iff_exists_witness bad exponent p).2
    ⟨q, hqbad, hqp, hq⟩

/-- With only one bad prime, the off-diagonal gcd is the empty gcd `0`.
Thus every candidate prime divides it and there is no distinct witness. -/
theorem singleton_offDiagonalGcd
    (exponent : ℕ → ℕ) (p : ℕ) :
    offDiagonalGcd {p} exponent p = 0 := by
  simp [offDiagonalGcd]

/-- The one-bad-prime edge case is always exceptional for a method requiring
a distinct auxiliary bad prime. -/
theorem singleton_candidate_divides_offDiagonalGcd
    (exponent : ℕ → ℕ) (p : ℕ) :
    p ∣ offDiagonalGcd {p} exponent p := by
  simp [singleton_offDiagonalGcd]

/-- An off-diagonal exponent equal to one supplies a witness for every
candidate `p ≠ 1`. -/
theorem unit_exponent_forces_not_dvd
    {bad : Finset ℕ} {exponent : ℕ → ℕ} {p q : ℕ}
    (hp : p ≠ 1) (hqbad : q ∈ bad) (hqp : q ≠ p)
    (hexponent : exponent q = 1) :
    ¬ p ∣ offDiagonalGcd bad exponent p := by
  apply witness_forces_not_dvd_offDiagonalGcd hqbad hqp
  intro hdiv
  apply hp
  exact Nat.dvd_one.mp (by simpa [hexponent] using hdiv)

#print axioms dvd_offDiagonalGcd_iff
#print axioms not_dvd_offDiagonalGcd_iff_exists_witness
#print axioms witness_forces_not_dvd_offDiagonalGcd
#print axioms singleton_offDiagonalGcd
#print axioms singleton_candidate_divides_offDiagonalGcd
#print axioms unit_exponent_forces_not_dvd

end SemistablePrimeCertificate
end MillenniumBSD
