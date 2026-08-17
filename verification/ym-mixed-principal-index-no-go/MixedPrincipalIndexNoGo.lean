import Mathlib

namespace Millennium.YangMills.MixedPrincipalIndexNoGo

theorem principal_pair_contains_diagonal
    {ι : Type*} [DecidableEq ι]
    (J : Finset ι) {α : ι} (hα : α ∈ J) :
    (α, α) ∈ J ×ˢ J := by
  simp [hα]

theorem no_nonempty_principal_index_set_all_cross
    {ι κ : Type*} [DecidableEq ι]
    (cell : ι → κ) (J : Finset ι)
    (hcross : ∀ {α β : ι}, α ∈ J → β ∈ J → cell α ≠ cell β) :
    J = ∅ := by
  ext α
  simp only [Finset.mem_empty, iff_false]
  intro hα
  exact (hcross hα hα) rfl

#print axioms principal_pair_contains_diagonal
#print axioms no_nonempty_principal_index_set_all_cross

end Millennium.YangMills.MixedPrincipalIndexNoGo
