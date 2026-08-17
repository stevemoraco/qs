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
  constructor
  · intro hα
    have hf : False := (hcross hα hα) rfl
    exact hf.elim
  · intro hα
    have hf : False := by simpa using hα
    exact hf.elim

#print axioms principal_pair_contains_diagonal
#print axioms no_nonempty_principal_index_set_all_cross

end Millennium.YangMills.MixedPrincipalIndexNoGo
