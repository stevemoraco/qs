import Mathlib

/-!
# Round 211 Hodge exceptional-sector finite cores

This file formalizes only finite algebraic and logical implications used in the
Round 211 audit. It does not formalize blow-ups, Chow groups, motives, group
actions on varieties, Hodge structures, algebraic cycles, or the Hodge
conjecture.
-/

namespace Millennium
namespace Round211Hodge

/-- A nonzero idempotent in a group algebra acts nontrivially on the regular
module: applying it to the identity vector returns the idempotent itself, and
the resulting vector is fixed by the idempotent. -/
theorem group_algebra_idempotent_survives_regular_copy
    {G : Type*} [Group G]
    (e : MonoidAlgebra ℚ G)
    (hne : e ≠ 0)
    (hid : e * e = e) :
    e * (1 : MonoidAlgebra ℚ G) ≠ 0 ∧
      e * (e * (1 : MonoidAlgebra ℚ G)) =
        e * (1 : MonoidAlgebra ℚ G) := by
  constructor
  · simpa using hne
  · calc
      e * (e * (1 : MonoidAlgebra ℚ G)) =
          (e * e) * (1 : MonoidAlgebra ℚ G) :=
        (mul_assoc e e (1 : MonoidAlgebra ℚ G)).symm
      _ = e * (1 : MonoidAlgebra ℚ G) := by rw [hid]

/-- If an algebraic set is stable under an idempotent and contains a vector
whose projection is nonzero, then the projected sector contains a nonzero
algebraic vector fixed by the idempotent. -/
theorem stable_algebraic_set_meets_nonzero_idempotent_image
    {V : Type*} [Zero V]
    (algebraic : Set V)
    (e : V → V)
    (hid : ∀ x, e (e x) = e x)
    (hstable : ∀ x ∈ algebraic, e x ∈ algebraic)
    (x : V)
    (hx : x ∈ algebraic)
    (hne : e x ≠ 0) :
    ∃ y, y ∈ algebraic ∧ y ≠ 0 ∧ e y = y := by
  exact ⟨e x, hstable x hx, hne, hid x⟩

/-- The composition of two commuting idempotent functions is idempotent. This
is the finite algebra behind composing a character projector with an
exceptional-complement or intersection-cohomology projector. -/
theorem commuting_idempotents_comp_idempotent
    {V : Type*}
    (e f : V → V)
    (he : ∀ x, e (e x) = e x)
    (hf : ∀ x, f (f x) = f x)
    (hcomm : ∀ x, e (f x) = f (e x)) :
    ∀ x, e (f (e (f x))) = e (f x) := by
  intro x
  calc
    e (f (e (f x))) = e (e (f (f x))) := by
      rw [← hcomm (f x)]
    _ = e (f (f x)) := by rw [he (f (f x))]
    _ = e (f x) := by rw [hf x]

/-- If a class is fixed by a projector compatible with the cycle map, then
nonmembership in the projected cycle image certifies nonmembership in the full
cycle image. -/
theorem fixed_class_outside_projected_cycle_image_is_not_cycle
    {Cycle Cohomology : Type*}
    (cycleClass : Cycle → Cohomology)
    (qCycle : Cycle → Cycle)
    (qCohomology : Cohomology → Cohomology)
    (hcompat : ∀ z, qCohomology (cycleClass z) = cycleClass (qCycle z))
    (alpha : Cohomology)
    (hfixed : qCohomology alpha = alpha)
    (houtside : ¬ ∃ z, cycleClass (qCycle z) = alpha) :
    ¬ ∃ z, cycleClass z = alpha := by
  intro hcycle
  rcases hcycle with ⟨z, hz⟩
  apply houtside
  refine ⟨z, ?_⟩
  calc
    cycleClass (qCycle z) = qCohomology (cycleClass z) :=
      (hcompat z).symm
    _ = qCohomology alpha := by rw [hz]
    _ = alpha := hfixed

#print axioms group_algebra_idempotent_survives_regular_copy
#print axioms stable_algebraic_set_meets_nonzero_idempotent_image
#print axioms commuting_idempotents_comp_idempotent
#print axioms fixed_class_outside_projected_cycle_image_is_not_cycle

end Round211Hodge
end Millennium
