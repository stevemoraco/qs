import Mathlib

namespace Millennium.YangMills.TransferDefectTightnessCore

open Finset

theorem high_spectral_weight_le_half
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight transfer : ι → ℝ) (high : Finset ι) {delta : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (htransfer : ∀ i, transfer i ≤ 1)
    (hdelta : 0 < delta)
    (hhigh : ∀ i ∈ high, delta ≤ 1 - transfer i)
    (hbudget :
      (∑ i, weight i * (1 - transfer i)) ≤
        delta * ((∑ i, weight i) / 2)) :
    (∑ i ∈ high, weight i) ≤ (∑ i, weight i) / 2 := by
  have hcost :
      delta * (∑ i ∈ high, weight i) ≤
        ∑ i ∈ high, weight i * (1 - transfer i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hmul := mul_le_mul_of_nonneg_right (hhigh i hi) (hweight i)
    simpa [mul_comm] using hmul
  have hsector :
      (∑ i ∈ high, weight i * (1 - transfer i)) ≤
        ∑ i, weight i * (1 - transfer i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ high
    · intro i hi hnot
      exact mul_nonneg (hweight i) (sub_nonneg.mpr (htransfer i))
  have hfinal :
      delta * (∑ i ∈ high, weight i) ≤
        delta * ((∑ i, weight i) / 2) :=
    hcost.trans (hsector.trans hbudget)
  nlinarith [hfinal]

#print axioms high_spectral_weight_le_half

end Millennium.YangMills.TransferDefectTightnessCore
