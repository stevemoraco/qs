import Mathlib
namespace B4Auto20Run2

theorem hodge_subtract_known_submodule_term
    {M : Type} [AddCommGroup M] [Module ℚ M]
    (S : Submodule ℚ M) {x y : M}
    (hxy : x + y ∈ S) (hy : y ∈ S) :
    x ∈ S := by
  have hsub : (x + y) - y ∈ S := S.sub_mem hxy hy
  simpa using hsub

theorem hodge_aggregate_membership_does_not_force_summand :
    ((1 : ℚ) + (-1) ∈ (⊥ : Submodule ℚ ℚ)) ∧
    ((1 : ℚ) ∉ (⊥ : Submodule ℚ ℚ)) := by
  simp

#print axioms hodge_subtract_known_submodule_term
#print axioms hodge_aggregate_membership_does_not_force_summand
end B4Auto20Run2
