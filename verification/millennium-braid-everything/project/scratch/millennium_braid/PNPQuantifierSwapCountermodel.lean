import Mathlib

/-!
# P vs NP hardness-magnification quantifier countermodel

This formalizes only the logical point that

  `∀ k, ∃ L, Hard k L`

does not imply

  `∃ L, ∀ k, Hard k L`.

It does not prove or disprove P vs NP.
-/

namespace Millennium
namespace PNPQuantifierSwap

/-- Toy hardness relation: language index `L` beats size exponent `k` exactly when `k < L`. -/
def Hard (k L : ℕ) : Prop := k < L

/-- For every fixed exponent there is some witness beating it. -/
theorem every_exponent_has_a_witness : ∀ k : ℕ, ∃ L : ℕ, Hard k L := by
  intro k
  exact ⟨k + 1, by simp [Hard]⟩

/-- No single witness beats all exponents. -/
theorem no_single_witness_beats_every_exponent : ¬ ∃ L : ℕ, ∀ k : ℕ, Hard k L := by
  rintro ⟨L, hL⟩
  have := hL L
  simp [Hard] at this

/-- Explicit countermodel to the invalid quantifier swap. -/
theorem quantifier_swap_invalid :
    (∀ k : ℕ, ∃ L : ℕ, Hard k L) ∧
    ¬ (∃ L : ℕ, ∀ k : ℕ, Hard k L) := by
  exact ⟨every_exponent_has_a_witness, no_single_witness_beats_every_exponent⟩

end PNPQuantifierSwap
end Millennium
