import Mathlib

namespace Millennium.Hodge.SecantSelfIntersection

variable {α : Type*}

/-- BANKER: if a proposed secant locus contains the original locus, then
intersecting the original locus with that secant locus returns the whole
original locus. -/
theorem banker_secant_containment_forces_self_intersection
    {X Sec : Set α} (h : X ⊆ Sec) :
    X ∩ Sec = X := by
  exact Set.inter_eq_left.mpr h

/-- CRITIC: a nested intersection need not be proper; the one-point model
already returns the entire left-hand locus. -/
theorem critic_expected_proper_intersection_fails :
    let X : Set (Fin 1) := Set.univ
    let Sec : Set (Fin 1) := Set.univ
    X ⊆ Sec ∧ X ∩ Sec = X ∧ X.Nonempty := by
  simp

/-- CLEANER: an intersection with `X` differs from `X` exactly when `X` is
not contained in the other locus.  Thus any genuine positive-codimension
intersection argument must first prove noncontainment. -/
theorem cleaner_nonwhole_intersection_iff_noncontainment
    {X Sec : Set α} :
    X ∩ Sec ≠ X ↔ ¬ X ⊆ Sec := by
  exact not_congr Set.inter_eq_left

#print axioms banker_secant_containment_forces_self_intersection
#print axioms critic_expected_proper_intersection_fails
#print axioms cleaner_nonwhole_intersection_iff_noncontainment

end Millennium.Hodge.SecantSelfIntersection
