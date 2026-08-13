import Mathlib

/-!
# Finite countermodel for Hodge projector-transfer logic

This formalizes only the elementary linear-algebra obstruction:
an idempotent rational projector need not preserve a distinguished
"algebraic-class" subspace.  It does not prove or disprove Hodge.
-/

namespace Millennium
namespace HodgeProjectorCountermodel

abbrev V := ℚ × ℚ

/-- Distinguished subspace standing in for algebraic cycle classes. -/
def Algebraic (v : V) : Prop := v.2 = 0

/-- Projection onto the second coordinate axis along the line spanned by `(1,-1)`. -/
def e (v : V) : V := (0, v.1 + v.2)

/-- The projector is genuinely idempotent. -/
theorem e_idempotent (v : V) : e (e v) = e v := by
  simp [e]

/-- Every projected vector lies on the second coordinate axis. -/
theorem e_first_coordinate_zero (v : V) : (e v).1 = 0 := by
  simp [e]

/-- Every vector on the second coordinate axis is fixed by the projector. -/
theorem e_fixes_second_axis (y : ℚ) : e (0, y) = (0, y) := by
  simp [e]

/-- The designated algebraic vector `(1,0)` is sent outside the designated
algebraic subspace. -/
theorem algebraic_not_preserved :
    Algebraic (1, 0) ∧ ¬ Algebraic (e (1, 0)) := by
  constructor
  · simp [Algebraic]
  · simp [Algebraic, e]

/-- Hence idempotence alone cannot imply preservation of an arbitrary
distinguished subspace. -/
theorem idempotent_projector_counterexample :
    (∀ v : V, e (e v) = e v) ∧
    (∃ v : V, Algebraic v ∧ ¬ Algebraic (e v)) := by
  constructor
  · exact e_idempotent
  · exact ⟨(1, 0), algebraic_not_preserved⟩

end HodgeProjectorCountermodel
end Millennium
