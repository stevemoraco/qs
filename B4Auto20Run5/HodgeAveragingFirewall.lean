import Mathlib

namespace B4Auto20Run5

/-- BANKER: a rational subspace is closed under rational averaging. Thus an
averaging/projector construction is safe only after every averaged summand has
already been proved to lie in the algebraic-cycle subspace. -/
theorem hodge_rational_average_preserves_submodule
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : Submodule ℚ V) (x y : V) (hx : x ∈ S) (hy : y ∈ S) :
    (1 / 2 : ℚ) • x + (1 / 2 : ℚ) • y ∈ S := by
  exact S.add_mem (S.smul_mem (1 / 2 : ℚ) hx) (S.smul_mem (1 / 2 : ℚ) hy)

/-- CRITIC: membership of an average does not imply membership of the summands.
The average of `1` and `-1` is zero, which lies in the bottom rational subspace,
although neither nonzero summand does. Cancellation can therefore fake
algebraicity at the aggregate level. -/
theorem hodge_average_membership_does_not_identify_summands :
    let S : Submodule ℚ ℚ := ⊥
    ((1 / 2 : ℚ) • (1 : ℚ) + (1 / 2 : ℚ) • (-1 : ℚ) ∈ S) ∧
    (1 : ℚ) ∉ S ∧ (-1 : ℚ) ∉ S := by
  norm_num

/-- CLEANER: if the average lies in the subspace and one summand is already
known to lie there, then the other summand can be recovered because the
coefficient `1/2` is nonzero. This isolates the exact extra input an averaging
argument needs to avoid the cancellation obstruction. -/
theorem hodge_average_and_one_summand_exactify_other
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : Submodule ℚ V) (x y : V) (hy : y ∈ S)
    (havg : (1 / 2 : ℚ) • x + (1 / 2 : ℚ) • y ∈ S) :
    x ∈ S := by
  have hyhalf : (1 / 2 : ℚ) • y ∈ S := S.smul_mem (1 / 2 : ℚ) hy
  have hxhalf : (1 / 2 : ℚ) • x ∈ S := by
    have hsub := S.sub_mem havg hyhalf
    simpa using hsub
  have htwo : (2 : ℚ) • ((1 / 2 : ℚ) • x) ∈ S := S.smul_mem (2 : ℚ) hxhalf
  simpa [smul_smul] using htwo

#print axioms B4Auto20Run5.hodge_rational_average_preserves_submodule
#print axioms B4Auto20Run5.hodge_average_membership_does_not_identify_summands
#print axioms B4Auto20Run5.hodge_average_and_one_summand_exactify_other

end B4Auto20Run5
