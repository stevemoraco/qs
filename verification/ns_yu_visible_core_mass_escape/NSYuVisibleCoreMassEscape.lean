import Mathlib

/-!
# Yu visible-core mass-escape countermodel

Finite real algebra only.

This file sanity-checks the normalization obstruction to passing from global
canonical projective concentration to concentration on a fixed visible core.
It does **not** formalize integration, conditional measures, Navier--Stokes,
Runlong Yu's estimate, smooth profile extraction, or any Clay theorem.
-/

namespace NSYuVisibleCoreMassEscape

def globalDefectNumerator (R : ℝ) : ℝ :=
  2 * (R ^ 4 + R ^ 2 + 1)

def globalMass (R : ℝ) : ℝ :=
  R ^ 3 + 2

theorem exact_three_atom_energy_ledger (R : ℝ) :
    globalDefectNumerator R =
      (1 + R ^ 2) + (1 + R ^ 2) + 2 * R ^ 4 := by
  simp [globalDefectNumerator]
  ring

theorem exact_three_atom_mass_ledger (R : ℝ) :
    globalMass R = 1 + 1 + R ^ 3 := by
  simp [globalMass]
  ring

theorem fixed_core_impurity :
    1 - (((1 : ℝ) / 2) ^ 2 + ((1 : ℝ) / 2) ^ 2 + 0 ^ 2) = (1 : ℝ) / 2 := by
  norm_num

theorem explicit_small_global_defect_at_100 :
    globalDefectNumerator (100 : ℝ) / (globalMass (100 : ℝ)) ^ 2 <
      (1 : ℝ) / 1000 := by
  norm_num [globalDefectNumerator, globalMass]

theorem explicit_core_mass_escape_at_100 :
    (2 : ℝ) / globalMass (100 : ℝ) < (1 : ℝ) / 100000 := by
  norm_num [globalMass]

theorem scaled_global_defect_bound (R : ℝ) (hR : 1 ≤ R) :
    globalDefectNumerator R * R ^ 2 ≤ 6 * (globalMass R) ^ 2 := by
  have hR0 : 0 ≤ R := by linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hR4 : R ^ 2 ≤ R ^ 4 := by
    nlinarith [sq_nonneg (R ^ 2 - 1)]
  have h1R4 : 1 ≤ R ^ 4 := by linarith
  have hnum : globalDefectNumerator R ≤ 6 * R ^ 4 := by
    simp [globalDefectNumerator]
    nlinarith
  have hmass : R ^ 6 ≤ (globalMass R) ^ 2 := by
    simp [globalMass]
    have hR3 : 0 ≤ R ^ 3 := by positivity
    nlinarith
  have hR2nonneg : 0 ≤ R ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnum hR2nonneg
  calc
    globalDefectNumerator R * R ^ 2 ≤ 6 * R ^ 4 * R ^ 2 := by
      simpa [mul_assoc] using hmul
    _ = 6 * R ^ 6 := by ring
    _ ≤ 6 * (globalMass R) ^ 2 := by nlinarith

theorem conditional_budget_division
    (m E EB : ℝ) (hm : 0 < m)
    (hrestrict : m ^ 2 * EB ≤ E) :
    EB ≤ E / m ^ 2 := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  exact (le_div_iff₀ hm2).2 hrestrict

#print axioms exact_three_atom_energy_ledger
#print axioms exact_three_atom_mass_ledger
#print axioms fixed_core_impurity
#print axioms explicit_small_global_defect_at_100
#print axioms explicit_core_mass_escape_at_100
#print axioms scaled_global_defect_bound
#print axioms conditional_budget_division

end NSYuVisibleCoreMassEscape
