import Mathlib

/-!
# Exact mutual-exclusivity no-shortcut theorem

Mutual exclusivity says only that a proposition and its negation cannot both
hold. It supplies no rule selecting the positive side, even for a finite family
of six or eight targets.
-/

namespace MillenniumGrandExclusivity

/-- No uniform rule can turn any finite family of mutual-exclusivity facts into
all positive members. The singleton family `False` is the smallest hostile
counterinstance. -/
theorem finite_exclusivities_cannot_choose_all :
    ¬ (∀ n : ℕ, ∀ P : Fin n → Prop,
      (∀ i, ¬ (P i ∧ ¬ P i)) → ∀ i, P i) := by
  intro chooseAll
  exact chooseAll 1 (fun _ : Fin 1 => False) (by simp) 0

/-- Exact arity for the six open Clay propositions. -/
theorem six_exclusivities_cannot_choose_all :
    ¬ (∀ A B C D E F : Prop,
      (¬ (A ∧ ¬ A) ∧ ¬ (B ∧ ¬ B) ∧ ¬ (C ∧ ¬ C) ∧
       ¬ (D ∧ ¬ D) ∧ ¬ (E ∧ ¬ E) ∧ ¬ (F ∧ ¬ F)) →
      A ∧ B ∧ C ∧ D ∧ E ∧ F) := by
  intro chooseAll
  exact (chooseAll False True True True True True (by simp)).1

/-- Exact arity for six open Clay propositions, the Poincare/Perelman slot,
and the seventh-object inversion coordinate. -/
theorem eight_exclusivities_cannot_choose_all :
    ¬ (∀ A B C D E F G H : Prop,
      (¬ (A ∧ ¬ A) ∧ ¬ (B ∧ ¬ B) ∧ ¬ (C ∧ ¬ C) ∧
       ¬ (D ∧ ¬ D) ∧ ¬ (E ∧ ¬ E) ∧ ¬ (F ∧ ¬ F) ∧
       ¬ (G ∧ ¬ G) ∧ ¬ (H ∧ ¬ H)) →
      A ∧ B ∧ C ∧ D ∧ E ∧ F ∧ G ∧ H) := by
  intro chooseAll
  exact (chooseAll False True True True True True True True (by simp)).1

structure ExclusivityFirewall : Prop where
  noFiniteChooser :
    ¬ (∀ n : ℕ, ∀ P : Fin n → Prop,
      (∀ i, ¬ (P i ∧ ¬ P i)) → ∀ i, P i)
  noSixChooser :
    ¬ (∀ A B C D E F : Prop,
      (¬ (A ∧ ¬ A) ∧ ¬ (B ∧ ¬ B) ∧ ¬ (C ∧ ¬ C) ∧
       ¬ (D ∧ ¬ D) ∧ ¬ (E ∧ ¬ E) ∧ ¬ (F ∧ ¬ F)) →
      A ∧ B ∧ C ∧ D ∧ E ∧ F)
  noEightChooser :
    ¬ (∀ A B C D E F G H : Prop,
      (¬ (A ∧ ¬ A) ∧ ¬ (B ∧ ¬ B) ∧ ¬ (C ∧ ¬ C) ∧
       ¬ (D ∧ ¬ D) ∧ ¬ (E ∧ ¬ E) ∧ ¬ (F ∧ ¬ F) ∧
       ¬ (G ∧ ¬ G) ∧ ¬ (H ∧ ¬ H)) →
      A ∧ B ∧ C ∧ D ∧ E ∧ F ∧ G ∧ H)

theorem exclusivity_firewall : ExclusivityFirewall where
  noFiniteChooser := finite_exclusivities_cannot_choose_all
  noSixChooser := six_exclusivities_cannot_choose_all
  noEightChooser := eight_exclusivities_cannot_choose_all

#print axioms finite_exclusivities_cannot_choose_all
#print axioms six_exclusivities_cannot_choose_all
#print axioms eight_exclusivities_cannot_choose_all
#print axioms exclusivity_firewall

end MillenniumGrandExclusivity
