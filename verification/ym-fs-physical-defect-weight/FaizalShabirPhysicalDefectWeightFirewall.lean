import Mathlib

/-!
# Faizal--Shabir physical defect-weight firewall

Finite real-algebra facts used in a hostile audit of arXiv:2606.19362v1,
especially Theorem 11.1 equations (11.6)--(11.8).

The paper's displayed coefficient after converting a one-step transfer defect
to a Hamiltonian-gap defect is

  exp (a_k * Delta_k) / a_(k+1).

On a continuum refinement with a_(k+1) -> 0 this coefficient is not uniformly
bounded merely from a_k >= 0 and Delta_k >= 0. A raw defect of order a_(k+1)
can therefore have order-one cost after physical normalization.

This file formalizes only that scalar unit/normalization firewall. It does not
formalize transfer operators, Yang--Mills theory, Osterwalder--Schrader
reconstruction, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirPhysicalDefectWeightFirewall

/-- The one-step transfer spectral edge `1 - exp(-x)` is at most the
physical dimensionless energy `x`. In particular, when `x = a * Delta` tends
to zero, a fixed positive Hamiltonian gap does not give a regulator-uniform
positive one-step transfer edge. -/
theorem transfer_edge_gap_le_scaled_energy (x : ℝ) :
    1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- A small scaled energy immediately makes the one-step transfer edge small. -/
theorem transfer_edge_gap_le_of_scaled_energy_le
    (x ε : ℝ)
    (hscale : x ≤ ε) :
    1 - Real.exp (-x) ≤ ε := by
  exact (transfer_edge_gap_le_scaled_energy x).trans hscale

/-- The physical defect coefficient is at least `1 / aNext` whenever the
current spacing and Hamiltonian gap are nonnegative. -/
theorem physical_defect_weight_coeff_lower_bound
    (aNext a gap : ℝ)
    (haNext : 0 < aNext)
    (ha : 0 ≤ a)
    (hgap : 0 ≤ gap) :
    1 / aNext ≤ Real.exp (a * gap) / aNext := by
  have hprod : 0 ≤ a * gap := mul_nonneg ha hgap
  have hexp0 : Real.exp 0 ≤ Real.exp (a * gap) := Real.exp_le_exp.mpr hprod
  have hone : 1 ≤ Real.exp (a * gap) := by
    simpa using hexp0
  have hinv : 0 ≤ (1 / aNext) := le_of_lt (one_div_pos.mpr haNext)
  have hmul := mul_le_mul_of_nonneg_right hone hinv
  simpa [div_eq_mul_inv] using hmul

/-- The coefficient `1/aNext` can be arbitrarily large as the next spacing is
allowed to shrink: every prescribed positive value occurs exactly. -/
theorem inverse_spacing_coefficient_realizes_any_positive_value
    (M : ℝ)
    (hM : 0 < M) :
    ∃ aNext : ℝ, 0 < aNext ∧ 1 / aNext = M := by
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  simp

/-- A raw one-step defect exactly of order the next lattice spacing has unit
cost after multiplication by `1/aNext`. Thus `O(aNext)` is not a vanishing
physical defect budget; one needs `o(aNext)` or a stronger cancellation. -/
theorem spacing_sized_raw_defect_has_unit_physical_cost
    (aNext : ℝ)
    (haNext : 0 < aNext) :
    (1 / aNext) * aNext = 1 := by
  field_simp [haNext.ne']

/-- Repeating a spacing-sized raw defect over `n` regulator steps gives exact
normalized debt `n`, even though each individual raw defect can be arbitrarily
small. -/
theorem repeated_spacing_sized_defects_accumulate_linearly
    (n : ℕ)
    (aNext : ℝ)
    (haNext : 0 < aNext) :
    (Finset.range n).sum (fun _k => (1 / aNext) * aNext) = (n : ℝ) := by
  calc
    (Finset.range n).sum (fun _k => (1 / aNext) * aNext) =
        (Finset.range n).sum (fun _k => (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact spacing_sized_raw_defect_has_unit_physical_cost aNext haNext
    _ = (n : ℝ) := by simp

#print axioms transfer_edge_gap_le_scaled_energy
#print axioms transfer_edge_gap_le_of_scaled_energy_le
#print axioms physical_defect_weight_coeff_lower_bound
#print axioms inverse_spacing_coefficient_realizes_any_positive_value
#print axioms spacing_sized_raw_defect_has_unit_physical_cost
#print axioms repeated_spacing_sized_defects_accumulate_linearly

end Millennium.YangMills.FaizalShabirPhysicalDefectWeightFirewall
