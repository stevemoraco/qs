import Mathlib

/-!
# Hodge very-general spread: finite logical core

This file formalizes only the final witness-transfer logic after one proper
surjective equality component has already been constructed.

It does not formalize complex varieties, Baire category, relative Chow spaces,
cycle classes, local systems, Hodge loci, or the Hodge Conjecture.
-/

namespace MillenniumBraid
namespace HodgeVeryGeneralSpreadFinite

/-- A surjective parameter family whose every point carries a witness for its
image supplies a witness over every base point. -/
theorem every_fiber_has_witness_of_surjective_family
    {C S W : Type*}
    (q : C → S)
    (witness : C → W)
    (Represents : W → S → Prop)
    (hsurj : Function.Surjective q)
    (hrep : ∀ c, Represents (witness c) (q c)) :
    ∀ s, ∃ w, Represents w s := by
  intro s
  obtain ⟨c, rfl⟩ := hsurj s
  exact ⟨witness c, hrep c⟩

/-- The same conclusion retains the actual parameter point, useful when the
witness must be pulled back from a universal family. -/
theorem every_fiber_has_parameter_and_witness
    {C S W : Type*}
    (q : C → S)
    (witness : C → W)
    (Represents : W → S → Prop)
    (hsurj : Function.Surjective q)
    (hrep : ∀ c, Represents (witness c) (q c)) :
    ∀ s, ∃ c, q c = s ∧ Represents (witness c) s := by
  intro s
  obtain ⟨c, hc⟩ := hsurj s
  refine ⟨c, hc, ?_⟩
  simpa [hc] using hrep c

/-- If one fixed parameter type dominates, no per-fiber change of complexity
index is needed. -/
theorem one_uniform_type_closes_all_fibers
    {I C S W : Type*}
    (i : I)
    (q : C → S)
    (witness : I → C → W)
    (Represents : I → W → S → Prop)
    (hsurj : Function.Surjective q)
    (hrep : ∀ c, Represents i (witness i c) (q c)) :
    ∀ s, ∃ w, Represents i w s := by
  intro s
  obtain ⟨c, rfl⟩ := hsurj s
  exact ⟨witness i c, hrep c⟩

/-- Dense coverage alone has no such formal consequence: the missing hypothesis
is represented abstractly by failure of surjectivity. -/
theorem missing_base_point_blocks_witness_transfer
    {C S : Type*}
    (q : C → S)
    (s : S)
    (hmiss : ∀ c, q c ≠ s) :
    ¬ ∃ c, q c = s := by
  rintro ⟨c, hc⟩
  exact hmiss c hc

#print axioms every_fiber_has_witness_of_surjective_family
#print axioms every_fiber_has_parameter_and_witness
#print axioms one_uniform_type_closes_all_fibers
#print axioms missing_base_point_blocks_witness_transfer

end HodgeVeryGeneralSpreadFinite
end MillenniumBraid
