import Mathlib

namespace B4.Run22.Hodge

theorem banker_two_sector_ext {A B : Type*} {x y : A × B}
    (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) :
    x = y := by
  exact Prod.ext h₁ h₂

theorem critic_one_sector_projection_not_total :
    ∃ x y : Bool × Bool, x.1 = y.1 ∧ x ≠ y := by
  exact ⟨(false, false), (false, true), rfl, by decide⟩

theorem cleaner_pair_eq_iff_both_sector_eq {A B : Type*} {x y : A × B} :
    x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h₁, h₂⟩
    exact banker_two_sector_ext h₁ h₂

#print axioms banker_two_sector_ext
#print axioms critic_one_sector_projection_not_total
#print axioms cleaner_pair_eq_iff_both_sector_eq

end B4.Run22.Hodge
