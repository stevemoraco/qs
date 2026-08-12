import Mathlib

namespace B4Auto20Run3

theorem hodge_projector_membership_bridge
    {α : Type*} (P : α → α) (S : Set α) {x y : α}
    (hmap : Set.MapsTo P S S) (hx : x ∈ S) (hxy : P x = y) :
    y ∈ S := by
  simpa [hxy] using hmap hx

theorem hodge_idempotence_does_not_imply_preservation :
    ∃ (P : Bool → Bool) (S : Set Bool),
      (∀ x, P (P x) = P x) ∧
      ∃ x, x ∈ S ∧ P x ∉ S := by
  refine ⟨(fun _ : Bool => true), ({false} : Set Bool), ?_, ?_⟩
  · intro x
    rfl
  · exact ⟨false, by simp, by simp⟩

#print axioms B4Auto20Run3.hodge_projector_membership_bridge
#print axioms B4Auto20Run3.hodge_idempotence_does_not_imply_preservation

end B4Auto20Run3
