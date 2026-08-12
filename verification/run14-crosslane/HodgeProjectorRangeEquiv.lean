import Mathlib

namespace MillenniumHodgeProjector

/-- For a fixed class and a cycle-compatible projector, ambient-cycle
representability is exactly projected-cycle representability. -/
theorem hodge_projector_range_equiv
    {Z H : Type*}
    (cl : Z → H)
    (pH : H → H)
    (pZ : Z → Z)
    (alpha : H)
    (hfix : pH alpha = alpha)
    (hcompat : ∀ z, pH (cl z) = cl (pZ z)) :
    alpha ∈ Set.range cl ↔
      alpha ∈ Set.range (fun z => cl (pZ z)) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      cl (pZ z) = pH (cl z) := (hcompat z).symm
      _ = pH alpha := by rw [hz]
      _ = alpha := hfix
  · rintro ⟨z, hz⟩
    exact ⟨pZ z, hz⟩

/-- Contrapositive form: under the same hypotheses, the two
nonrepresentability statements are equivalent. -/
theorem hodge_projector_nonrange_equiv
    {Z H : Type*}
    (cl : Z → H)
    (pH : H → H)
    (pZ : Z → Z)
    (alpha : H)
    (hfix : pH alpha = alpha)
    (hcompat : ∀ z, pH (cl z) = cl (pZ z)) :
    alpha ∉ Set.range cl ↔
      alpha ∉ Set.range (fun z => cl (pZ z)) := by
  constructor
  · intro hAmbient hProjected
    apply hAmbient
    exact (hodge_projector_range_equiv cl pH pZ alpha hfix hcompat).mpr hProjected
  · intro hProjected hAmbient
    apply hProjected
    exact (hodge_projector_range_equiv cl pH pZ alpha hfix hcompat).mp hAmbient

#print axioms hodge_projector_range_equiv
#print axioms hodge_projector_nonrange_equiv

end MillenniumHodgeProjector
