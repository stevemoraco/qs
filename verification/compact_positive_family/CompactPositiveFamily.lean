import Mathlib

namespace CompactPositiveFamily

theorem compact_finite_positive_family
    {X : Type*} {ι : Type*} [TopologicalSpace X]
    {K : Set X}
    (hK : IsCompact K)
    (f : ι → X → ℝ)
    (hcont : ∀ i, Continuous (f i))
    (hnonneg : ∀ i x, 0 ≤ f i x)
    (hpoint : ∀ x ∈ K, ∃ i, 0 < f i x) :
    ∃ t : Finset ι, ∃ v : ℝ, 0 < v ∧
      ∀ x ∈ K, v ≤ ∑ i ∈ t, f i x := by
  let U : ι → Set X := fun i => {x | 0 < f i x}
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    exact isOpen_lt continuous_const (hcont i)
  have hcover : K ⊆ ⋃ i, U i := by
    intro x hx
    rcases hpoint x hx with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  rcases hK.elim_finite_subcover U hUopen hcover with ⟨t, ht⟩
  let total : X → ℝ := fun x => ∑ i ∈ t, f i x
  have htotal_cont : Continuous total := by
    dsimp [total]
    fun_prop
  have htotal_pos : ∀ x ∈ K, 0 < total x := by
    intro x hx
    have hxcover := ht hx
    rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
    rcases Set.mem_iUnion.mp hxi with ⟨hi, hpos⟩
    have hsingle : f i x ≤ total x := by
      dsimp [total]
      exact Finset.single_le_sum
        (fun j hj => hnonneg j x) hi
    exact lt_of_lt_of_le hpos hsingle
  rcases hK.exists_forall_le' htotal_cont.continuousOn htotal_pos with
    ⟨v, hv, hlower⟩
  exact ⟨t, v, hv, hlower⟩

#print axioms compact_finite_positive_family

end CompactPositiveFamily
