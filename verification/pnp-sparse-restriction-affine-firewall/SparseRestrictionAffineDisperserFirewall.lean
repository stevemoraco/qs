import Mathlib

namespace Millennium
namespace PNP
namespace SparseRestrictionAffineDisperserFirewall

theorem card_lower_of_every_fiber_nonempty
    {α β : Type*}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β))
    (h : ∀ a : α, ∃ b : β, (a, b) ∈ S) :
    Fintype.card α ≤ S.card := by
  let I : Finset α := S.image (fun x : α × β => x.1)
  have huniv : Finset.univ ⊆ I := by
    intro a ha
    obtain ⟨b, hb⟩ := h a
    exact Finset.mem_image.mpr ⟨(a, b), hb, rfl⟩
  have himage : (S.image (fun x : α × β => x.1)).card ≤ S.card := by
    exact Finset.card_image_le
  calc
    Fintype.card α = Finset.univ.card := by simp
    _ ≤ I.card := Finset.card_le_card huniv
    _ ≤ S.card := by simpa [I] using himage

theorem missing_fiber_of_card_lt
    {α β : Type*}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β))
    (hsmall : S.card < Fintype.card α) :
    ∃ a : α, ∀ b : β, (a, b) ∉ S := by
  classical
  by_contra hmiss
  have hall : ∀ a : α, ∃ b : β, (a, b) ∈ S := by
    intro a
    by_contra ha
    apply hmiss
    refine ⟨a, ?_⟩
    intro b hb
    exact ha ⟨b, hb⟩
  have hlarge := card_lower_of_every_fiber_nonempty S hall
  omega

theorem boolean_prefix_card (q : ℕ) :
    Fintype.card (Fin q → Bool) = 2 ^ q := by
  simp

theorem sparse_boolean_support_has_empty_prefix_fiber
    (q d : ℕ)
    (S : Finset ((Fin q → Bool) × (Fin d → Bool)))
    (hsmall : S.card < 2 ^ q) :
    ∃ a : Fin q → Bool, ∀ b : Fin d → Bool, (a, b) ∉ S := by
  apply missing_fiber_of_card_lt S
  simpa [boolean_prefix_card] using hsmall

theorem positive_support_lower_bound
    {α β : Type*}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (P : α × β → Prop) [DecidablePred P]
    (hpos : ∀ a : α, ∃ b : β, P (a, b)) :
    Fintype.card α ≤ (Finset.univ.filter P).card := by
  apply card_lower_of_every_fiber_nonempty
  intro a
  obtain ⟨b, hb⟩ := hpos a
  exact ⟨b, by simp [hb]⟩

theorem two_sided_support_lower_bounds
    {α β : Type*}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (P : α × β → Prop) [DecidablePred P]
    (hpos : ∀ a : α, ∃ b : β, P (a, b))
    (hneg : ∀ a : α, ∃ b : β, ¬ P (a, b)) :
    Fintype.card α ≤ (Finset.univ.filter P).card ∧
      Fintype.card α ≤ (Finset.univ.filter (fun x => ¬ P x)).card := by
  constructor
  · exact positive_support_lower_bound P hpos
  · exact positive_support_lower_bound (fun x => ¬ P x) hneg

theorem boolean_prefix_nonconstant_forces_positive_density
    (q d : ℕ)
    (P : (Fin q → Bool) × (Fin d → Bool) → Prop)
    [DecidablePred P]
    (hpos : ∀ a : Fin q → Bool, ∃ b : Fin d → Bool, P (a, b)) :
    2 ^ q ≤ (Finset.univ.filter P).card := by
  simpa [boolean_prefix_card] using
    (positive_support_lower_bound P hpos)

theorem boolean_prefix_nonconstant_forces_two_sided_density
    (q d : ℕ)
    (P : (Fin q → Bool) × (Fin d → Bool) → Prop)
    [DecidablePred P]
    (hpos : ∀ a : Fin q → Bool, ∃ b : Fin d → Bool, P (a, b))
    (hneg : ∀ a : Fin q → Bool, ∃ b : Fin d → Bool, ¬ P (a, b)) :
    2 ^ q ≤ (Finset.univ.filter P).card ∧
      2 ^ q ≤ (Finset.univ.filter (fun x => ¬ P x)).card := by
  simpa [boolean_prefix_card] using
    (two_sided_support_lower_bounds P hpos hneg)

#print axioms card_lower_of_every_fiber_nonempty
#print axioms missing_fiber_of_card_lt
#print axioms boolean_prefix_card
#print axioms sparse_boolean_support_has_empty_prefix_fiber
#print axioms positive_support_lower_bound
#print axioms two_sided_support_lower_bounds
#print axioms boolean_prefix_nonconstant_forces_positive_density
#print axioms boolean_prefix_nonconstant_forces_two_sided_density

end SparseRestrictionAffineDisperserFirewall
end PNP
end Millennium
