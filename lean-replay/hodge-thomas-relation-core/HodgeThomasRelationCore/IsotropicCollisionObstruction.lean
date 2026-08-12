import Mathlib

/-!
# A non-isotropic vanishing-cycle relation

This file gives a two-dimensional exact countermodel to the claim that every
linear relation among vanishing cycles can be supported on a pairwise
orthogonal collection. It is a finite linear-algebra obstruction only. It
does not assert that this exact configuration occurs in a particular
hyperplane-section family, and it does not prove or disprove the Hodge
conjecture.

There are no user-declared axioms or proof placeholders.
-/

namespace HodgeThomasRelationCore
namespace IsotropicCollisionObstruction

variable {𝕜 : Type*} [Field 𝕜]

/-- The standard alternating form on a two-dimensional vector space. -/
def omega (x y : 𝕜 × 𝕜) : 𝕜 := x.1 * y.2 - x.2 * y.1

/-- First basis vanishing vector. -/
def e : 𝕜 × 𝕜 := (1, 0)

/-- Second basis vanishing vector. -/
def f : 𝕜 × 𝕜 := (0, 1)

/-- Their sum. -/
def d : 𝕜 × 𝕜 := (1, 1)

/-- Every relation among `e`, `f`, and `d=e+f` is a scalar multiple of
`(-1,-1,1)`. -/
theorem relation_normal_form (a b c : 𝕜)
    (hrel : a • e + b • f + c • d = 0) :
    a = -c ∧ b = -c := by
  have hfirst := congrArg Prod.fst hrel
  have hsecond := congrArg Prod.snd hrel
  constructor
  · simp [e, f, d] at hfirst
    linear_combination hfirst
  · simp [e, f, d] at hsecond
    linear_combination hsecond

/-- Any nonzero relation uses all three vectors. -/
theorem nonzero_relation_uses_all_three (a b c : 𝕜)
    (hrel : a • e + b • f + c • d = 0)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
  obtain ⟨ha, hb⟩ := relation_normal_form a b c hrel
  have hc : c ≠ 0 := by
    intro hc0
    have ha0 : a = 0 := by simpa [ha, hc0]
    have hb0 : b = 0 := by simpa [hb, hc0]
    rcases hnonzero with hane | hbne | hcne
    · exact hane ha0
    · exact hbne hb0
    · exact hcne hc0
  refine ⟨?_, ?_, hc⟩
  · simpa [ha] using neg_ne_zero.mpr hc
  · simpa [hb] using neg_ne_zero.mpr hc

/-- The three required vectors are pairwise nonorthogonal for the standard
alternating form. -/
theorem required_pairings_nonzero :
    omega (e : 𝕜 × 𝕜) f ≠ 0 ∧
    omega (e : 𝕜 × 𝕜) d ≠ 0 ∧
    omega (f : 𝕜 × 𝕜) d ≠ 0 := by
  simp [omega, e, f, d]

/-- Consequently, this relation space contains no nonzero relation whose
support is pairwise orthogonal: every nonzero relation uses all three vectors,
and every pair among them has nonzero intersection. -/
theorem nonzero_relation_forces_nonorthogonal_support (a b c : 𝕜)
    (hrel : a • e + b • f + c • d = 0)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    omega (e : 𝕜 × 𝕜) f ≠ 0 ∧
    omega (e : 𝕜 × 𝕜) d ≠ 0 ∧
    omega (f : 𝕜 × 𝕜) d ≠ 0 := by
  obtain ⟨ha, hb, hc⟩ := nonzero_relation_uses_all_three a b c hrel hnonzero
  obtain ⟨hef, hed, hfd⟩ := (required_pairings_nonzero (𝕜 := 𝕜))
  exact ⟨ha, hb, hc, hef, hed, hfd⟩

end IsotropicCollisionObstruction
end HodgeThomasRelationCore
