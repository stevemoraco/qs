import Mathlib

/-!
# Finite empty-fiber core

This file formalizes the pigeonhole lemma underlying the sparsity barrier to
a universal affine-disperser gate-elimination transplant. It does not
formalize vector spaces, affine subspaces, circuit lower bounds, sparse NP
languages, or P versus NP.

There are no user-declared axioms or proof placeholders.
-/

namespace PNPOPSSlopeCore

theorem exists_unhit_value_of_card_lt
    {α β : Type*} [Fintype β]
    (P : Finset α) (π : α → β)
    (hcard : P.card < Fintype.card β) :
    ∃ y : β, ∀ x : α, x ∈ P → π x ≠ y := by
  classical
  by_contra hnone
  push_neg at hnone
  have himage : P.image π = (Finset.univ : Finset β) := by
    apply Finset.eq_univ_of_forall
    intro y
    obtain ⟨x, hx, hxy⟩ := hnone y
    exact Finset.mem_image.mpr ⟨x, hx, hxy⟩
  have hle : (P.image π).card ≤ P.card := Finset.card_image_le
  rw [himage] at hle
  have hcodomain_le : Fintype.card β ≤ P.card := by
    simpa using hle
  exact (not_lt_of_ge hcodomain_le) hcard

theorem card_codomain_le_of_every_value_hit
    {α β : Type*} [Fintype β]
    (P : Finset α) (π : α → β)
    (hhit : ∀ y : β, ∃ x : α, x ∈ P ∧ π x = y) :
    Fintype.card β ≤ P.card := by
  by_contra hnot
  have hcard : P.card < Fintype.card β := Nat.lt_of_not_ge hnot
  obtain ⟨y, hy⟩ := exists_unhit_value_of_card_lt P π hcard
  obtain ⟨x, hx, hxy⟩ := hhit y
  exact (hy x hx) hxy

end PNPOPSSlopeCore
