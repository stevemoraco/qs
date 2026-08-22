import Mathlib

/-!
# BSD restricted rank-zero finite-prime reduction: finite logical core

Honesty status: this file formalizes only the elementary prime-cutoff and
support-gluing logic used after the arithmetic local theorems have already been
supplied.

It does not formalize elliptic curves, L-functions, Néron periods, Tamagawa
numbers, Tate--Shafarevich groups, Galois representations, Manin constants,
Kolyvagin systems, Castella--Sano, Skinner, or BSD.
-/

namespace MillenniumBraid
namespace BSDPrimeSupportFinite

/-- Every prime at most eleven is one of the five small primes. -/
theorem prime_le_eleven_classification
    (p : ℕ) (hp : p.Prime) (hle : p ≤ 11) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have hp2 : 2 ≤ p := hp.two_le
  have h4 : p ≠ 4 := by
    intro h
    subst p
    norm_num at hp
  have h6 : p ≠ 6 := by
    intro h
    subst p
    norm_num at hp
  have h8 : p ≠ 8 := by
    intro h
    subst p
    norm_num at hp
  have h9 : p ≠ 9 := by
    intro h
    subst p
    norm_num at hp
  have h10 : p ≠ 10 := by
    intro h
    subst p
    norm_num at hp
  omega

/-- Every prime at most eleven divides `2310 = 2*3*5*7*11`. -/
theorem prime_le_eleven_dvd_2310
    (p : ℕ) (hp : p.Prime) (hle : p ≤ 11) :
    p ∣ 2310 := by
  rcases prime_le_eleven_classification p hp hle with
    rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- A prime not dividing `2310` lies above eleven. -/
theorem prime_gt_eleven_of_not_dvd_2310
    (p : ℕ) (hp : p.Prime) (hnot : ¬ p ∣ 2310) :
    11 < p := by
  by_contra h
  have hle : p ≤ 11 := Nat.le_of_not_gt h
  exact hnot (prime_le_eleven_dvd_2310 p hp hle)

/--
If a local assertion is known at every prime above eleven and at the five small
primes, then it is known at every prime.
-/
theorem all_primes_of_large_and_five
    (LocalOK : ℕ → Prop)
    (hlarge : ∀ p, p.Prime → 11 < p → LocalOK p)
    (h2 : LocalOK 2)
    (h3 : LocalOK 3)
    (h5 : LocalOK 5)
    (h7 : LocalOK 7)
    (h11 : LocalOK 11) :
    ∀ p, p.Prime → LocalOK p := by
  intro p hp
  by_cases hlargep : 11 < p
  · exact hlarge p hp hlargep
  · have hle : p ≤ 11 := Nat.le_of_not_gt hlargep
    rcases prime_le_eleven_classification p hp hle with
      rfl | rfl | rfl | rfl | rfl
    · exact h2
    · exact h3
    · exact h5
    · exact h7
    · exact h11

/--
If every large-prime valuation vanishes, any prime supporting a nonzero
valuation is among the five small primes.
-/
theorem nonzero_support_is_small
    (valuation : ℕ → ℤ)
    (hlarge : ∀ p, p.Prime → 11 < p → valuation p = 0)
    (p : ℕ) (hp : p.Prime) (hnonzero : valuation p ≠ 0) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  by_contra hsmall
  have hnotle : ¬ p ≤ 11 := by
    intro hle
    exact hsmall (prime_le_eleven_classification p hp hle)
  have hgt : 11 < p := Nat.lt_of_not_ge hnotle
  exact hnonzero (hlarge p hp hgt)

/--
Abstract finite-support form: after all nonexceptional local assertions are
known, global completion is exactly the remaining exceptional assertions.
-/
theorem completion_from_exceptional_set
    {α : Type*}
    (Exceptional : Set α)
    (LocalOK : α → Prop)
    (houtside : ∀ x, x ∉ Exceptional → LocalOK x)
    (hinside : ∀ x, x ∈ Exceptional → LocalOK x) :
    ∀ x, LocalOK x := by
  intro x
  by_cases hx : x ∈ Exceptional
  · exact hinside x hx
  · exact houtside x hx

#print axioms prime_le_eleven_classification
#print axioms prime_le_eleven_dvd_2310
#print axioms prime_gt_eleven_of_not_dvd_2310
#print axioms all_primes_of_large_and_five
#print axioms nonzero_support_is_small
#print axioms completion_from_exceptional_set

end BSDPrimeSupportFinite
end MillenniumBraid
