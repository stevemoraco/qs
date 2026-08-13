import Mathlib

namespace B4.Run21.Hodge

theorem banker_product_injective {A B C D : Type*} {f : A → C} {g : B → D}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (fun p : A × B => (f p.1, g p.2)) := by
  intro p q hpq
  apply Prod.ext
  · exact hf (congrArg Prod.fst hpq)
  · exact hg (congrArg Prod.snd hpq)

theorem critic_first_sector_injective_not_total :
    Function.Injective (fun b : Bool => b) ∧
      ¬ Function.Injective (fun p : Bool × Bool => (p.1, ())) := by
  constructor
  · intro a b h
    exact h
  · intro h
    have hp : (false, false) = (false, true) := h rfl
    have hbad : (false : Bool) = true := congrArg Prod.snd hp
    simpa using hbad

theorem cleaner_product_injective_iff {A B C D : Type*}
    (a0 : A) (b0 : B) (f : A → C) (g : B → D) :
    Function.Injective (fun p : A × B => (f p.1, g p.2)) ↔
      Function.Injective f ∧ Function.Injective g := by
  constructor
  · intro h
    constructor
    · intro a a' ha
      have hp : (a, b0) = (a', b0) := h (by simp [ha])
      exact congrArg Prod.fst hp
    · intro b b' hb
      have hp : (a0, b) = (a0, b') := h (by simp [hb])
      exact congrArg Prod.snd hp
  · rintro ⟨hf, hg⟩
    exact banker_product_injective hf hg

#print axioms banker_product_injective
#print axioms critic_first_sector_injective_not_total
#print axioms cleaner_product_injective_iff

end B4.Run21.Hodge
