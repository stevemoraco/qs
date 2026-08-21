import Mathlib

namespace BSD
namespace C487PairingBlindnessFinite

variable {A T : Type*} [AddCommGroup A] [AddCommGroup T]

theorem cyclic_alternating_pairing_zero
    (B : A →+ A →+ T)
    (g : A)
    (hcyclic : ∀ x : A, ∃ n : ℤ, n • g = x)
    (halt : ∀ x : A, B x x = 0) :
    ∀ x y : A, B x y = 0 := by
  intro x y
  obtain ⟨m, hm⟩ := hcyclic x
  obtain ⟨n, hn⟩ := hcyclic y
  rw [← hm, ← hn]
  simp [halt g]

theorem finite_layer_never_bounds_tower (n : ℕ) :
    ∃ m : ℕ, n < m := by
  exact ⟨n + 1, Nat.lt_succ_self n⟩

theorem finite_menu_has_deeper_layer
    (depths : Finset ℕ) :
    ∃ m : ℕ, ∀ n ∈ depths, n < m := by
  refine ⟨depths.sup id + 1, ?_⟩
  intro n hn
  exact Nat.lt_succ_of_le (Finset.le_sup hn)

theorem one_finite_primary_excludes_everywhere_divisible
    {P : Type*}
    (finitePrimary divisiblePrimary : P → Prop)
    (hincompatible : ∀ p, finitePrimary p → divisiblePrimary p → False)
    (hallDivisible : ∀ p, divisiblePrimary p)
    (p : P)
    (hfinite : finitePrimary p) : False := by
  exact hincompatible p hfinite (hallDivisible p)

theorem one_prime_selects_good_state
    {P : Type*}
    (good bad : Prop)
    (finitePrimary divisiblePrimary : P → Prop)
    (hdichotomy : good ∨ bad)
    (hbadDivisible : bad → ∀ p, divisiblePrimary p)
    (hincompatible : ∀ p, finitePrimary p → divisiblePrimary p → False)
    (p : P)
    (hfinite : finitePrimary p) : good := by
  rcases hdichotomy with hgood | hbad
  · exact hgood
  · exact False.elim
      (hincompatible p hfinite (hbadDivisible hbad p))

#print axioms cyclic_alternating_pairing_zero
#print axioms finite_menu_has_deeper_layer
#print axioms one_finite_primary_excludes_everywhere_divisible
#print axioms one_prime_selects_good_state

end C487PairingBlindnessFinite
end BSD
