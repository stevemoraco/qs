import Mathlib

/-!
# Source-root extraction and fixed-handoff preservation

Finite real-analysis core for a source-decorated connected expansion.

The displayed source norm weights a first source derivative by `sigma` and a
second source derivative by `sigma^2 / 2`.  If a connected support joining two
source buffers has tree length at least their separation, the same weighted
row pays the physical root-to-root exponential.  Fixed bounded handoffs then
change only the prefactor, not the exponent.

The first theorem also records the typing firewall: an unrooted row cannot
control a passive root coefficient unless a source/root insertion estimate is
actually supplied.

This file does not formalize Banach-valued holomorphy, replica--BKAR, Kirk's
activity spaces, renormalization, continuum Yang--Mills theory, a mass gap, or
an official prize theorem.
-/

namespace Millennium.YangMills.SourceRootExtractionFinite

/-- An invisible passive-root coefficient can be arbitrarily large while the
unrooted coordinate is exactly zero. -/
theorem hidden_root_row_not_controlled_by_unrooted_row (C : ℝ) :
    ∃ root : ℝ, 0 < root ∧ C * 0 < root := by
  have hroot : 0 < max (C + 1) 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right (C + 1) 1)
  refine ⟨max (C + 1) 1, hroot, ?_⟩
  rw [mul_zero]
  exact hroot

/-- Moving from a support-tree length `tau` to a smaller root separation `d`
preserves an exponentially weighted bound. -/
theorem root_path_weight_transfer
    (kappa d tau row envelope : ℝ)
    (hkappa : 0 ≤ kappa)
    (hdt : d ≤ tau)
    (hrow : 0 ≤ row)
    (hweighted : Real.exp (kappa * tau) * row ≤ envelope) :
    Real.exp (kappa * d) * row ≤ envelope := by
  have harg : kappa * d ≤ kappa * tau :=
    mul_le_mul_of_nonneg_left hdt hkappa
  have hexp : Real.exp (kappa * d) ≤ Real.exp (kappa * tau) :=
    Real.exp_le_exp.mpr harg
  calc
    Real.exp (kappa * d) * row ≤ Real.exp (kappa * tau) * row :=
      mul_le_mul_of_nonneg_right hexp hrow
    _ ≤ envelope := hweighted

/-- First-source-order extraction in denominator-cleared form. -/
theorem one_source_root_path_extraction
    (sigma kappa d tau row envelope : ℝ)
    (hsigma : 0 ≤ sigma)
    (hkappa : 0 ≤ kappa)
    (hdt : d ≤ tau)
    (hrow : 0 ≤ row)
    (hweighted :
      Real.exp (kappa * tau) * (sigma * row) ≤ envelope) :
    sigma * Real.exp (kappa * d) * row ≤ envelope := by
  have hscaled : 0 ≤ sigma * row := mul_nonneg hsigma hrow
  have hpath :=
    root_path_weight_transfer
      kappa d tau (sigma * row) envelope hkappa hdt hscaled hweighted
  calc
    sigma * Real.exp (kappa * d) * row =
        Real.exp (kappa * d) * (sigma * row) := by ring
    _ ≤ envelope := hpath

/-- Second-source-order extraction.  The factor `2` is the exact `2!` cost
coming from the factorial source normalization. -/
theorem two_source_root_path_extraction
    (sigma kappa d tau row envelope : ℝ)
    (hkappa : 0 ≤ kappa)
    (hdt : d ≤ tau)
    (hrow : 0 ≤ row)
    (hweighted :
      Real.exp (kappa * tau) * ((sigma ^ 2 / 2) * row) ≤ envelope) :
    sigma ^ 2 * Real.exp (kappa * d) * row ≤ 2 * envelope := by
  have hscaled : 0 ≤ (sigma ^ 2 / 2) * row := by positivity
  have hpath :=
    root_path_weight_transfer
      kappa d tau ((sigma ^ 2 / 2) * row) envelope
      hkappa hdt hscaled hweighted
  calc
    sigma ^ 2 * Real.exp (kappa * d) * row =
        2 * (Real.exp (kappa * d) * ((sigma ^ 2 / 2) * row)) := by ring
    _ ≤ 2 * envelope := mul_le_mul_of_nonneg_left hpath (by norm_num)

/-- A fixed bounded output map preserves the physical root exponent and costs
only its prefactor `K`. -/
theorem fixed_handoff_preserves_root_exponent
    (sigma kappa d input output K envelope : ℝ)
    (hK : 0 ≤ K)
    (hmap : output ≤ K * input)
    (hinput :
      sigma ^ 2 * Real.exp (kappa * d) * input ≤ 2 * envelope) :
    sigma ^ 2 * Real.exp (kappa * d) * output ≤ 2 * K * envelope := by
  have hfactor : 0 ≤ sigma ^ 2 * Real.exp (kappa * d) := by positivity
  calc
    sigma ^ 2 * Real.exp (kappa * d) * output ≤
        (sigma ^ 2 * Real.exp (kappa * d)) * (K * input) :=
      mul_le_mul_of_nonneg_left hmap hfactor
    _ = K * (sigma ^ 2 * Real.exp (kappa * d) * input) := by ring
    _ ≤ K * (2 * envelope) := mul_le_mul_of_nonneg_left hinput hK
    _ = 2 * K * envelope := by ring

/-- Directly compose two-source extraction with one fixed output handoff. -/
theorem two_source_extraction_after_handoff
    (sigma kappa d tau input output K envelope : ℝ)
    (hkappa : 0 ≤ kappa)
    (hdt : d ≤ tau)
    (hinput_nonneg : 0 ≤ input)
    (hK : 0 ≤ K)
    (hmap : output ≤ K * input)
    (hweighted :
      Real.exp (kappa * tau) * ((sigma ^ 2 / 2) * input) ≤ envelope) :
    sigma ^ 2 * Real.exp (kappa * d) * output ≤ 2 * K * envelope := by
  have hextracted :=
    two_source_root_path_extraction
      sigma kappa d tau input envelope
      hkappa hdt hinput_nonneg hweighted
  exact
    fixed_handoff_preserves_root_exponent
      sigma kappa d input output K envelope hK hmap hextracted

/-- Six uniformly bounded one-step maps produce one fixed composite root-row
constant. -/
theorem six_bounded_root_handoffs
    (K1 K2 K3 K4 K5 K6 r0 r1 r2 r3 r4 r5 r6 : ℝ)
    (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hK4 : 0 ≤ K4) (hK5 : 0 ≤ K5) (hK6 : 0 ≤ K6)
    (h1 : r1 ≤ K1 * r0)
    (h2 : r2 ≤ K2 * r1)
    (h3 : r3 ≤ K3 * r2)
    (h4 : r4 ≤ K4 * r3)
    (h5 : r5 ≤ K5 * r4)
    (h6 : r6 ≤ K6 * r5) :
    r6 ≤ (K6 * K5 * K4 * K3 * K2 * K1) * r0 := by
  calc
    r6 ≤ K6 * r5 := h6
    _ ≤ K6 * (K5 * r4) := mul_le_mul_of_nonneg_left h5 hK6
    _ = (K6 * K5) * r4 := by ring
    _ ≤ (K6 * K5) * (K4 * r3) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hK6 hK5)
    _ = (K6 * K5 * K4) * r3 := by ring
    _ ≤ (K6 * K5 * K4) * (K3 * r2) :=
      mul_le_mul_of_nonneg_left h3
        (mul_nonneg (mul_nonneg hK6 hK5) hK4)
    _ = (K6 * K5 * K4 * K3) * r2 := by ring
    _ ≤ (K6 * K5 * K4 * K3) * (K2 * r1) :=
      mul_le_mul_of_nonneg_left h2
        (mul_nonneg (mul_nonneg (mul_nonneg hK6 hK5) hK4) hK3)
    _ = (K6 * K5 * K4 * K3 * K2) * r1 := by ring
    _ ≤ (K6 * K5 * K4 * K3 * K2) * (K1 * r0) :=
      mul_le_mul_of_nonneg_left h1
        (mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg hK6 hK5) hK4) hK3)
          hK2)
    _ = (K6 * K5 * K4 * K3 * K2 * K1) * r0 := by ring

#print axioms hidden_root_row_not_controlled_by_unrooted_row
#print axioms root_path_weight_transfer
#print axioms one_source_root_path_extraction
#print axioms two_source_root_path_extraction
#print axioms fixed_handoff_preserves_root_exponent
#print axioms two_source_extraction_after_handoff
#print axioms six_bounded_root_handoffs

end Millennium.YangMills.SourceRootExtractionFinite
