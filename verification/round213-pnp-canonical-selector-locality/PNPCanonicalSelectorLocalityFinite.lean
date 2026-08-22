import Mathlib

/-!
# Round 213 P-versus-NP canonical-selector locality finite cores

This file formalizes only finite cardinality, exponent, and countermodel facts.
It does not formalize Boolean circuits, marker languages, the polynomial or
exponential hierarchies, hardness magnification, P, NP, or P versus NP.
-/

namespace Millennium
namespace Round213PNP

abbrev Seed (r : ℕ) := Fin r → Bool
abbrev Selector (q : ℕ) := Fin q → Bool

/-- The full `q`-bit selector space has exactly `2^q` elements. -/
theorem selector_space_card (q : ℕ) :
    Fintype.card (Selector q) = 2 ^ q := by
  simp [Selector]

/-- The `r`-bit seed space has exactly `2^r` elements. -/
theorem seed_space_card (r : ℕ) :
    Fintype.card (Seed r) = 2 ^ r := by
  simp [Seed]

/-- Under an explicit cardinality gap, no short-seed expander can enumerate
all selectors. This does not say that its image contains no hard selector; it
records only the safe counting direction. -/
theorem short_seed_expander_not_surjective
    (r q : ℕ)
    (expand : Seed r → Selector q)
    (hgap : 2 ^ r < 2 ^ q) :
    ¬ Function.Surjective expand := by
  intro hsurj
  have hle : Fintype.card (Selector q) ≤ Fintype.card (Seed r) :=
    Fintype.card_le_of_surjective expand hsurj
  rw [selector_space_card, seed_space_card] at hle
  omega

/-- A tiny exact countermodel: the full selector universe contains selectors
outside the circuit-realizable image, while every selector produced by the
seed generator remains circuit-realizable. Thus global counting hardness does
not force hardness inside an arbitrary generated subfamily. -/
def tinyExpand (_ : Fin 1) : Fin 3 := 0

def tinyRealize (_ : Fin 1) : Fin 3 := 0

theorem global_hard_selector_does_not_force_generated_hard_selector :
    (¬ Function.Surjective tinyRealize) ∧
      (∀ s, ∃ c, tinyRealize c = tinyExpand s) := by
  constructor
  · intro hsurj
    rcases hsurj (1 : Fin 3) with ⟨c, hc⟩
    simpa [tinyRealize] using hc
  · intro s
    exact ⟨0, rfl⟩

/-- If an ambient length is `2^k`, a quadratic selector table already has
`2^(2k)` bits. This is the finite size relocation behind the succinct-locality
firewall. -/
def ambientLength (k : ℕ) : ℕ := 2 ^ k

def selectorTableLength (k : ℕ) : ℕ := (ambientLength k) ^ 2

theorem selector_table_is_exponential_in_binary_length (k : ℕ) :
    selectorTableLength k = 2 ^ (2 * k) := by
  calc
    selectorTableLength k = (2 ^ k) ^ 2 := by
      rfl
    _ = 2 ^ (k * 2) := (pow_mul 2 k 2).symm
    _ = 2 ^ (2 * k) := by rw [Nat.mul_comm k 2]

/-- A polynomial ambient running time becomes exponential in the binary length
parameter. -/
theorem ambient_polynomial_runtime_at_binary_length (k a : ℕ) :
    (ambientLength k) ^ a = 2 ^ (k * a) := by
  exact (pow_mul 2 k a).symm

/-- A polynomial in the fifth-power padded length remains only a polynomial in
`k`; this identity is kept separate from the previous exponential identity. -/
def paddedLength (k : ℕ) : ℕ := k ^ 5

theorem padded_polynomial_runtime_identity (k d : ℕ) :
    (paddedLength k) ^ d = k ^ (5 * d) := by
  exact (pow_mul k 5 d).symm

#print axioms selector_space_card
#print axioms seed_space_card
#print axioms short_seed_expander_not_surjective
#print axioms global_hard_selector_does_not_force_generated_hard_selector
#print axioms selector_table_is_exponential_in_binary_length
#print axioms ambient_polynomial_runtime_at_binary_length
#print axioms padded_polynomial_runtime_identity

end Round213PNP
end Millennium
