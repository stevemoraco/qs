import Mathlib

namespace B4.Run21.PNP

theorem banker_exclude_every_fixed_class {Upper : ℕ → Prop}
    (h : ∀ C, ¬ Upper C) :
    ¬ ∃ C, Upper C := by
  rintro ⟨C, hC⟩
  exact h C hC

theorem critic_one_fixed_class_does_not_exclude_union :
    ¬ ((¬ ((0 : ℕ) = 1)) → ¬ ∃ C : ℕ, C = 1) := by
  intro h
  have hzero : ¬ ((0 : ℕ) = 1) := by decide
  have hnone := h hzero
  exact hnone ⟨1, rfl⟩

theorem cleaner_union_exclusion_iff {Upper : ℕ → Prop} :
    (¬ ∃ C, Upper C) ↔ ∀ C, ¬ Upper C := by
  constructor
  · intro h C hC
    exact h ⟨C, hC⟩
  · exact banker_exclude_every_fixed_class

#print axioms banker_exclude_every_fixed_class
#print axioms critic_one_fixed_class_does_not_exclude_union
#print axioms cleaner_union_exclusion_iff

end B4.Run21.PNP
