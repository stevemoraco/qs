import Mathlib

namespace Millennium.YangMills.TransferDefectSpectralTightnessV2

open Finset

theorem covariance_defect_identity
    {ι : Type*} [Fintype ι]
    (weight transfer : ι → ℝ) :
    (∑ i, weight i) - (∑ i, weight i * transfer i) =
      ∑ i, weight i * (1 - transfer i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem high_weight_costs_transfer_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight transfer : ι → ℝ) (high : Finset ι) {delta : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hhigh : ∀ i ∈ high, delta ≤ 1 - transfer i) :
    delta * (∑ i ∈ high, weight i) ≤
      ∑ i ∈ high, weight i * (1 - transfer i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hmul := mul_le_mul_of_nonneg_right (hhigh i hi) (hweight i)
  simpa [mul_comm] using hmul

theorem sector_defect_le_total_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight transfer : ι → ℝ) (sector : Finset ι)
    (hweight : ∀ i, 0 ≤ weight i)
    (htransfer : ∀ i, transfer i ≤ 1) :
    (∑ i ∈ sector, weight i * (1 - transfer i)) ≤
      ∑ i, weight i * (1 - transfer i) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_univ sector
  · intro i hi hnot
    exact mul_nonneg (hweight i) (sub_nonneg.mpr (htransfer i))

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
        ∑ i ∈ high, weight i * (1 - transfer i) :=
    high_weight_costs_transfer_defect weight transfer high hweight hhigh
  have hsector :
      (∑ i ∈ high, weight i * (1 - transfer i)) ≤
        ∑ i, weight i * (1 - transfer i) :=
    sector_defect_le_total_defect weight transfer high hweight htransfer
  have hfinal :
      delta * (∑ i ∈ high, weight i) ≤
        delta * ((∑ i, weight i) / 2) :=
    hcost.trans (hsector.trans hbudget)
  exact (mul_le_mul_left hdelta).mp hfinal

theorem high_spectral_weight_le_half_of_covariance_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight transfer : ι → ℝ) (high : Finset ι) {delta : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (htransfer : ∀ i, transfer i ≤ 1)
    (hdelta : 0 < delta)
    (hhigh : ∀ i ∈ high, delta ≤ 1 - transfer i)
    (hcov :
      (∑ i, weight i) - (∑ i, weight i * transfer i) ≤
        delta * ((∑ i, weight i) / 2)) :
    (∑ i ∈ high, weight i) ≤ (∑ i, weight i) / 2 := by
  apply high_spectral_weight_le_half weight transfer high hweight htransfer hdelta hhigh
  rw [← covariance_defect_identity weight transfer]
  exact hcov

theorem high_spectral_weight_le_half_of_transfer_threshold
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight transfer : ι → ℝ) (high : Finset ι) {delta : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (htransfer : ∀ i, transfer i ≤ 1)
    (hdelta : 0 < delta)
    (hthreshold : ∀ i ∈ high, transfer i ≤ 1 - delta)
    (hcov :
      (∑ i, weight i) - (∑ i, weight i * transfer i) ≤
        delta * ((∑ i, weight i) / 2)) :
    (∑ i ∈ high, weight i) ≤ (∑ i, weight i) / 2 := by
  apply high_spectral_weight_le_half_of_covariance_defect
    weight transfer high hweight htransfer hdelta
  · intro i hi
    linarith [hthreshold i hi]
  · exact hcov

#print axioms covariance_defect_identity
#print axioms high_weight_costs_transfer_defect
#print axioms sector_defect_le_total_defect
#print axioms high_spectral_weight_le_half
#print axioms high_spectral_weight_le_half_of_covariance_defect
#print axioms high_spectral_weight_le_half_of_transfer_threshold

end Millennium.YangMills.TransferDefectSpectralTightnessV2
