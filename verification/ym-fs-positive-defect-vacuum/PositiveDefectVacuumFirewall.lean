import Mathlib

/-!
# Faizal--Shabir Appendix-D positive-defect/vacuum firewall

Finite matrix shadow of a load-bearing compatibility condition in the
fixed-physical-time Appendix-D route.

If a kernel has entrywise nonnegative coefficients in a representation where
the vacuum has strictly positive coordinates, then annihilating that vacuum
forces every kernel coefficient to vanish.  Consequently a genuinely nonzero
entrywise-positive defect cannot simultaneously annihilate a strictly positive
vacuum in the same coordinate representation.

This file deliberately does not assert that the paper's phrase "orthonormal
basis adapted to the OS cone" supplies such coordinates.  That representation
typing is the source-specific analytic gate isolated by the companion audit.
It also does not formalize OS reconstruction, transfer kernels, Yang--Mills,
a mass gap, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirPositiveDefectVacuumFirewall

/-- A nonnegative two-entry row with strictly positive vacuum weights has zero
weighted sum only when both kernel entries vanish. -/
theorem two_entry_nonnegative_row_annihilating_positive_vacuum_is_zero
    (r₁ r₂ v₁ v₂ : ℝ)
    (hr₁ : 0 ≤ r₁)
    (hr₂ : 0 ≤ r₂)
    (hv₁ : 0 < v₁)
    (hv₂ : 0 < v₂)
    (hzero : r₁ * v₁ + r₂ * v₂ = 0) :
    r₁ = 0 ∧ r₂ = 0 := by
  have h₁nonneg : 0 ≤ r₁ * v₁ := mul_nonneg hr₁ (le_of_lt hv₁)
  have h₂nonneg : 0 ≤ r₂ * v₂ := mul_nonneg hr₂ (le_of_lt hv₂)
  have h₁zero : r₁ * v₁ = 0 := by
    linarith
  have h₂zero : r₂ * v₂ = 0 := by
    linarith
  constructor
  · exact (mul_eq_zero.mp h₁zero).resolve_right (ne_of_gt hv₁)
  · exact (mul_eq_zero.mp h₂zero).resolve_right (ne_of_gt hv₂)

/-- Two nonnegative rows annihilating the same strictly positive two-coordinate
vacuum force the complete `2 x 2` kernel to vanish. -/
theorem two_by_two_nonnegative_kernel_annihilating_positive_vacuum_is_zero
    (r₀₀ r₀₁ r₁₀ r₁₁ v₀ v₁ : ℝ)
    (hr₀₀ : 0 ≤ r₀₀)
    (hr₀₁ : 0 ≤ r₀₁)
    (hr₁₀ : 0 ≤ r₁₀)
    (hr₁₁ : 0 ≤ r₁₁)
    (hv₀ : 0 < v₀)
    (hv₁ : 0 < v₁)
    (hrow₀ : r₀₀ * v₀ + r₀₁ * v₁ = 0)
    (hrow₁ : r₁₀ * v₀ + r₁₁ * v₁ = 0) :
    r₀₀ = 0 ∧ r₀₁ = 0 ∧ r₁₀ = 0 ∧ r₁₁ = 0 := by
  have h₀ :=
    two_entry_nonnegative_row_annihilating_positive_vacuum_is_zero
      r₀₀ r₀₁ v₀ v₁ hr₀₀ hr₀₁ hv₀ hv₁ hrow₀
  have h₁ :=
    two_entry_nonnegative_row_annihilating_positive_vacuum_is_zero
      r₁₀ r₁₁ v₀ v₁ hr₁₀ hr₁₁ hv₀ hv₁ hrow₁
  exact ⟨h₀.1, h₀.2, h₁.1, h₁.2⟩

/-- If one kernel coefficient is strictly positive, entrywise nonnegativity and
strict positivity of the vacuum rule out exact vacuum annihilation. -/
theorem nonzero_nonnegative_kernel_cannot_annihilate_positive_vacuum
    (r₀₀ r₀₁ r₁₀ r₁₁ v₀ v₁ : ℝ)
    (hr₀₀ : 0 < r₀₀)
    (hr₀₁ : 0 ≤ r₀₁)
    (hr₁₀ : 0 ≤ r₁₀)
    (hr₁₁ : 0 ≤ r₁₁)
    (hv₀ : 0 < v₀)
    (hv₁ : 0 < v₁) :
    ¬ (r₀₀ * v₀ + r₀₁ * v₁ = 0 ∧
       r₁₀ * v₀ + r₁₁ * v₁ = 0) := by
  intro h
  have hz :=
    two_by_two_nonnegative_kernel_annihilating_positive_vacuum_is_zero
      r₀₀ r₀₁ r₁₀ r₁₁ v₀ v₁
      (le_of_lt hr₀₀) hr₀₁ hr₁₀ hr₁₁ hv₀ hv₁ h.1 h.2
  linarith [hr₀₀]

/-- In the constant-vacuum normalization, a nonnegative two-entry row with zero
row sum is identically zero.  This is the direct finite analogue of a
nonnegative integral kernel `R(x',x)` satisfying `∫ R(x',x) dx = 0`. -/
theorem nonnegative_row_zero_mass_is_zero
    (r₁ r₂ : ℝ)
    (hr₁ : 0 ≤ r₁)
    (hr₂ : 0 ≤ r₂)
    (hzero : r₁ + r₂ = 0) :
    r₁ = 0 ∧ r₂ = 0 := by
  have h :=
    two_entry_nonnegative_row_annihilating_positive_vacuum_is_zero
      r₁ r₂ 1 1 hr₁ hr₂ (by norm_num) (by norm_num) (by simpa using hzero)
  exact h

#print axioms two_entry_nonnegative_row_annihilating_positive_vacuum_is_zero
#print axioms two_by_two_nonnegative_kernel_annihilating_positive_vacuum_is_zero
#print axioms nonzero_nonnegative_kernel_cannot_annihilate_positive_vacuum
#print axioms nonnegative_row_zero_mass_is_zero

end Millennium.YangMills.FaizalShabirPositiveDefectVacuumFirewall
