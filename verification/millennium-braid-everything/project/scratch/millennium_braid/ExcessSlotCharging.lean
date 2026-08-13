import Mathlib

/-!
# Excess-slot charging finite core

Finite combinatorial core for the P-vs-NP `2n` frontier.  It does not encode
circuit semantics and does not prove `P != NP`.
-/

namespace Millennium
namespace ExcessSlotCharging

/-- If witnesses inject into a finite excess-slot type, their number is at most
    the number of available excess slots. -/
theorem witness_card_le_slot_card
    {W S : Type*} [Fintype W] [Fintype S]
    (charge : W → S)
    (hcharge : Function.Injective charge) :
    Fintype.card W ≤ Fintype.card S := by
  exact Fintype.card_le_of_injective charge hcharge

/-- Scalar form used after identifying the slot cardinality with the exact
    fanout surplus `a+b`. -/
theorem witness_card_le_surplus
    {W S : Type*} [Fintype W] [Fintype S]
    (charge : W → S)
    (hcharge : Function.Injective charge)
    (a b : ℕ)
    (hslots : Fintype.card S = a + b) :
    Fintype.card W ≤ a + b := by
  rw [← hslots]
  exact witness_card_le_slot_card charge hcharge

/-- Once the exact circuit identity is supplied as a scalar equality, `s`
    charged witnesses force the same additive gate surplus. -/
theorem gate_lower_bound_of_charged_witnesses
    {W S : Type*} [Fintype W] [Fintype S]
    (charge : W → S)
    (hcharge : Function.Injective charge)
    (a b n g s : ℕ)
    (hslots : Fintype.card S = a + b)
    (hw : s ≤ Fintype.card W)
    (hgate : g = (2 * n - 2) + (a + b)) :
    (2 * n - 2) + s ≤ g := by
  have hws : Fintype.card W ≤ a + b :=
    witness_card_le_surplus charge hcharge a b hslots
  have hs : s ≤ a + b := le_trans hw hws
  rw [hgate]
  exact Nat.add_le_add_left hs (2 * n - 2)

end ExcessSlotCharging
end Millennium
