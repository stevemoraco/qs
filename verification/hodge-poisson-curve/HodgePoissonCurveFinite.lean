import Mathlib

/-!
# Complementary-plane tangent obstruction: finite subspace core

Honesty status: this file formalizes only the subspace logic used after the
local Hochschild/Ext obstruction has been reduced to tangent containment.

It does not formalize exterior powers, Poisson structures, coherent sheaves,
Hochschild cohomology, Ext, semiregularity, Markman's construction, algebraic
cycles, or the Hodge Conjecture.
-/

namespace MillenniumBraid
namespace HodgePoissonCurveFinite

variable {K V : Type*}
variable [DivisionRing K]
variable [AddCommGroup V] [Module K V]

/-- Any subspace contained in two disjoint subspaces is zero. -/
theorem eq_bot_of_le_disjoint
    (P₁ P₂ L : Submodule K V)
    (hdisjoint : Disjoint P₁ P₂)
    (h₁ : L ≤ P₁)
    (h₂ : L ≤ P₂) :
    L = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [← hdisjoint.eq_bot]
  exact ⟨h₁ hx, h₂ hx⟩

/-- A nonzero tangent subspace cannot be contained in both complementary
planes. -/
theorem not_le_both_of_ne_bot
    (P₁ P₂ L : Submodule K V)
    (hdisjoint : Disjoint P₁ P₂)
    (hL : L ≠ ⊥) :
    ¬ (L ≤ P₁ ∧ L ≤ P₂) := by
  rintro ⟨h₁, h₂⟩
  exact hL (eq_bot_of_le_disjoint P₁ P₂ L hdisjoint h₁ h₂)

/-- Elementwise form: a nonzero vector cannot lie in two disjoint subspaces. -/
theorem nonzero_not_mem_both
    (P₁ P₂ : Submodule K V)
    (hdisjoint : Disjoint P₁ P₂)
    (v : V)
    (hv : v ≠ 0) :
    ¬ (v ∈ P₁ ∧ v ∈ P₂) := by
  rintro ⟨h₁, h₂⟩
  have hvbot : v ∈ (⊥ : Submodule K V) := by
    rw [← hdisjoint.eq_bot]
    exact ⟨h₁, h₂⟩
  apply hv
  simpa using hvbot

#print axioms eq_bot_of_le_disjoint
#print axioms not_le_both_of_ne_bot
#print axioms nonzero_not_mem_both

end HodgePoissonCurveFinite
end MillenniumBraid
