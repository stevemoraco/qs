import Mathlib

namespace Millennium.Hodge.FiniteCore

theorem contained_intersection
    {α : Type*} {Y S : Set α} (h : Y ⊆ S) : S ∩ Y = Y := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h hx, hx⟩

theorem cycle_projector_transfer
    {Z H : Type}
    (cl : Z → H) (pH : H → H) (pZ : Z → Z) (alpha : H)
    (hfix : pH alpha = alpha)
    (hcompat : ∀ z, pH (cl z) = cl (pZ z)) :
    alpha ∈ Set.range cl ↔ alpha ∈ Set.range (fun z => cl (pZ z)) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      cl (pZ z) = pH (cl z) := (hcompat z).symm
      _ = pH alpha := by rw [hz]
      _ = alpha := hfix
  · rintro ⟨z, hz⟩
    exact ⟨pZ z, hz⟩

#print axioms contained_intersection
#print axioms cycle_projector_transfer

end Millennium.Hodge.FiniteCore
