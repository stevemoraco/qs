import Mathlib

namespace B4Auto20Run1.BSD

/-- BANKER/CLEANER: for a finite nonnegative defect ledger, total defect zero is equivalent to vanishing of every local defect. -/
theorem finite_nonnegative_defect_ledger_exact
    {ι : Type*} [Fintype ι]
    (d : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ d i) :
    (∑ i, d i = 0) ↔ ∀ i, d i = 0 := by
  classical
  constructor
  · intro hsum i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (f := d) (by
        intro j _
        exact hnonneg j)).mp hsum
    exact hzero i (Finset.mem_univ i)
  · intro hall
    simp [hall]

/-- A single opposite global bound closes the finite ledger exactly once every term is known nonnegative. -/
theorem nonnegative_ledger_total_nonpositive_forces_exact
    {ι : Type*} [Fintype ι]
    (d : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ d i)
    (htotal : (∑ i, d i) ≤ 0) :
    ∀ i, d i = 0 := by
  have hsum_nonneg : 0 ≤ ∑ i, d i := by
    exact Finset.sum_nonneg fun i _ => hnonneg i
  have hzero : (∑ i, d i) = 0 := le_antisymm htotal hsum_nonneg
  exact (finite_nonnegative_defect_ledger_exact d hnonneg).mp hzero

/-- CRITIC: exact information at one defect coordinate does not control the total ledger. -/
theorem one_vanishing_defect_can_hide_positive_total :
    ∃ d₁ d₂ : ℝ,
      0 ≤ d₁ ∧
      0 ≤ d₂ ∧
      d₁ = 0 ∧
      0 < d₁ + d₂ := by
  refine ⟨0, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms finite_nonnegative_defect_ledger_exact
#print axioms nonnegative_ledger_total_nonpositive_forces_exact
#print axioms one_vanishing_defect_can_hide_positive_total

end B4Auto20Run1.BSD
