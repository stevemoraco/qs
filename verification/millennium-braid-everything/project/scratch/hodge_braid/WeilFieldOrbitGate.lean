import Mathlib

namespace HodgeBraid

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- A `K`-stable class subspace containing a cyclic `K`-generator is the
whole target space.  This is the exact algebra behind the Weil field-orbit
repair. -/
theorem stable_submodule_of_cyclic_generator
    (A : Submodule K W) (w : W)
    (hw : w ∈ A)
    (hcyclic : Submodule.span K ({w} : Set W) = ⊤) :
    A = ⊤ := by
  apply top_unique
  rw [← hcyclic]
  exact Submodule.span_le.2 (Set.singleton_subset_iff.mpr hw)

/-- Without stability under the larger coefficient field, one generator only
forces containment of its scalar span. -/
theorem generator_only_gives_span
    (A : Submodule K W) (w : W) (hw : w ∈ A) :
    Submodule.span K ({w} : Set W) ≤ A := by
  exact Submodule.span_le.2 (Set.singleton_subset_iff.mpr hw)

/-- If a cyclic generator is nonzero, the ambient one-generator module cannot
be the zero submodule. -/
theorem cyclic_generator_nontrivial
    (w : W) (hw : w ≠ 0)
    (hcyclic : Submodule.span K ({w} : Set W) = ⊤) :
    (⊤ : Submodule K W) ≠ ⊥ := by
  intro h
  have : w = 0 := by
    have hwtop : w ∈ (⊤ : Submodule K W) := by simp
    rw [h] at hwtop
    simpa using hwtop
  exact hw this

end HodgeBraid
