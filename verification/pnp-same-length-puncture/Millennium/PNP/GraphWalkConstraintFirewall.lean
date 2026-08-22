import Mathlib

namespace Millennium.PNP.GraphWalkConstraint

abbrev ChoiceWalk (n : ℕ) := Fin n → Bool
abbrev LayerNode (n : ℕ) := Fin (n + 1) × Bool

theorem layerNode_card (n : ℕ) :
    Fintype.card (LayerNode n) = (n + 1) * 2 := by
  simp [LayerNode]

theorem choiceWalk_card (n : ℕ) :
    Fintype.card (ChoiceWalk n) = 2 ^ n := by
  simp [ChoiceWalk]

def correlated2 (w : ChoiceWalk 2) : Prop := w 0 = w 1

theorem every_local_value_extends (i : Fin 2) (b : Bool) :
    ∃ w : ChoiceWalk 2, correlated2 w ∧ w i = b := by
  refine ⟨fun _ => b, ?_, rfl⟩
  rfl

def mixed2 : ChoiceWalk 2 := fun i => if i = 0 then false else true

theorem mixed2_not_correlated : ¬ correlated2 mixed2 := by
  simp [correlated2, mixed2]

theorem all_local_extensions_do_not_force_global :
    (∀ i : Fin 2,
      ∃ w : ChoiceWalk 2, correlated2 w ∧ w i = mixed2 i) ∧
    ¬ correlated2 mixed2 := by
  constructor
  · intro i
    exact every_local_value_extends i (mixed2 i)
  · exact mixed2_not_correlated

theorem constrained_walk_exists_exact
    {n : ℕ} (P : ChoiceWalk n → Prop) :
    (∃ w : ChoiceWalk n, P w) ↔ ∃ a : Fin n → Bool, P a := by
  rfl

#print axioms layerNode_card
#print axioms choiceWalk_card
#print axioms all_local_extensions_do_not_force_global
#print axioms constrained_walk_exists_exact

end Millennium.PNP.GraphWalkConstraint
