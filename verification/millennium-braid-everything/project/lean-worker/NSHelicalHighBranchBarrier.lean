import Mathlib

/-!
# Helical high-branch retention firewall

Finite algebra only.  This file places side by side the two exact inequalities
used in the Navier--Stokes helical-packet research lane.

For ordered physical magnitudes `0 < ell < m < h`:

* same helicity gives high-child energy fraction `(m-ell)/(h-ell) < m/h`;
* flipping the low child's helicity gives `(m+ell)/(h+ell) > m/h`.

The sign of helicity therefore reverses the amplitude-versus-frequency tax.
No Euler or Navier--Stokes PDE statement is formalized here.
-/

namespace NSHelicalHighBranchBarrier

/-- The exact positive gap after cross multiplication in the same-helicity
case. -/
theorem retention_frequency_gap_identity
    {ell m h : ℝ} :
    m * (h - ell) - h * (m - ell) = ell * (h - m) := by
  ring

/-- Same-helicity high-child retention is strictly below inverse frequency
gain. -/
theorem high_branch_cross_inequality
    {ell m h : ℝ}
    (hell : 0 < ell)
    (hh : m < h) :
    h * (m - ell) < m * (h - ell) := by
  have hpos : 0 < ell * (h - m) :=
    mul_pos hell (sub_pos.mpr hh)
  nlinarith [retention_frequency_gap_identity (ell := ell) (m := m) (h := h)]

/-- Ratio form of the same-helicity barrier. -/
theorem high_branch_ratio_lt_inverse_gain
    {ell m h : ℝ}
    (hell : 0 < ell)
    (helm : ell < m)
    (hmh : m < h) :
    (m - ell) / (h - ell) < m / h := by
  have hhpos : 0 < h := lt_trans (lt_trans hell helm) hmh
  have hhlpos : 0 < h - ell := sub_pos.mpr (lt_trans helm hmh)
  apply (div_lt_div_iff₀ hhlpos hhpos).2
  exact high_branch_cross_inequality hell hmh

/-- If an exact same-helicity relay transfers high-child squared amplitude
according to `Rnew² (h-ell) = Rold² (m-ell)`, then squared-amplitude times
frequency strictly decreases. -/
theorem weighted_energy_frequency_decreases
    {ell m h Rold Rnew : ℝ}
    (hell : 0 < ell)
    (helm : ell < m)
    (hmh : m < h)
    (hRold : Rold ≠ 0)
    (htransfer : Rnew^2 * (h - ell) = Rold^2 * (m - ell)) :
    Rnew^2 * h < Rold^2 * m := by
  have hhlpos : 0 < h - ell := sub_pos.mpr (lt_trans helm hmh)
  have hR2 : 0 < Rold^2 := sq_pos_of_ne_zero hRold
  have hgap : h * (m - ell) < m * (h - ell) :=
    high_branch_cross_inequality hell hmh
  have hscaled :
      Rold^2 * (h * (m - ell)) < Rold^2 * (m * (h - ell)) :=
    mul_lt_mul_of_pos_left hgap hR2
  have hcross :
      (Rnew^2 * h) * (h - ell) < (Rold^2 * m) * (h - ell) := by
    calc
      (Rnew^2 * h) * (h - ell)
          = h * (Rnew^2 * (h - ell)) := by ring
      _ = h * (Rold^2 * (m - ell)) := by rw [htransfer]
      _ = Rold^2 * (h * (m - ell)) := by ring
      _ < Rold^2 * (m * (h - ell)) := hscaled
      _ = (Rold^2 * m) * (h - ell) := by ring
  exact (mul_lt_mul_right hhlpos).mp hcross

/-- Exact cross-multiplied identity for the mixed-helicity `(-,+,+)` case. -/
theorem mixed_retention_frequency_gap_identity
    {ell m h : ℝ} :
    h * (m + ell) - m * (h + ell) = ell * (h - m) := by
  ring

/-- Flipping the low child's helicity reverses the same-helicity inequality:
the high-child energy retention is now strictly *larger* than the inverse
frequency gain. -/
theorem mixed_high_branch_cross_inequality
    {ell m h : ℝ}
    (hell : 0 < ell)
    (hmh : m < h) :
    m * (h + ell) < h * (m + ell) := by
  have hpos : 0 < ell * (h - m) :=
    mul_pos hell (sub_pos.mpr hmh)
  nlinarith [mixed_retention_frequency_gap_identity
    (ell := ell) (m := m) (h := h)]

/-- Ratio form of the mixed-helicity escape. -/
theorem mixed_high_branch_ratio_gt_inverse_gain
    {ell m h : ℝ}
    (hell : 0 < ell)
    (helm : ell < m)
    (hmh : m < h) :
    m / h < (m + ell) / (h + ell) := by
  have hhpos : 0 < h := lt_trans (lt_trans hell helm) hmh
  have hhelpos : 0 < h + ell := add_pos hhpos hell
  apply (div_lt_div_iff₀ hhpos hhelpos).2
  exact mixed_high_branch_cross_inequality hell hmh

/-- If a mixed-helicity relay has the exact transfer law
`Rnew² (h+ell) = Rold² (m+ell)`, then squared-amplitude times frequency
strictly increases.  This is the finite algebraic escape from the
same-helicity `N^{-1/2}` tax. -/
theorem mixed_weighted_energy_frequency_increases
    {ell m h Rold Rnew : ℝ}
    (hell : 0 < ell)
    (helm : ell < m)
    (hmh : m < h)
    (hRold : Rold ≠ 0)
    (htransfer : Rnew^2 * (h + ell) = Rold^2 * (m + ell)) :
    Rold^2 * m < Rnew^2 * h := by
  have hhelpos : 0 < h + ell :=
    add_pos (lt_trans (lt_trans hell helm) hmh) hell
  have hR2 : 0 < Rold^2 := sq_pos_of_ne_zero hRold
  have hgap : m * (h + ell) < h * (m + ell) :=
    mixed_high_branch_cross_inequality hell hmh
  have hscaled :
      Rold^2 * (m * (h + ell)) < Rold^2 * (h * (m + ell)) :=
    mul_lt_mul_of_pos_left hgap hR2
  have hcross :
      (Rold^2 * m) * (h + ell) < (Rnew^2 * h) * (h + ell) := by
    calc
      (Rold^2 * m) * (h + ell)
          = Rold^2 * (m * (h + ell)) := by ring
      _ < Rold^2 * (h * (m + ell)) := hscaled
      _ = h * (Rold^2 * (m + ell)) := by ring
      _ = h * (Rnew^2 * (h + ell)) := by rw [← htransfer]
      _ = (Rnew^2 * h) * (h + ell) := by ring
  exact (mul_lt_mul_right hhelpos).mp hcross

/-- Exact 3-4-5 mixed-helicity energy fractions: coefficient magnitudes
`(-8,1,7)` send `7/8` of transferred energy to the high child. -/
theorem mixed_345_fraction :
    ((4 : ℚ) + 3) / (5 + 3) = (7 : ℚ) / 8 := by
  norm_num

#print axioms retention_frequency_gap_identity
#print axioms high_branch_cross_inequality
#print axioms high_branch_ratio_lt_inverse_gain
#print axioms weighted_energy_frequency_decreases
#print axioms mixed_retention_frequency_gap_identity
#print axioms mixed_high_branch_cross_inequality
#print axioms mixed_high_branch_ratio_gt_inverse_gain
#print axioms mixed_weighted_energy_frequency_increases
#print axioms mixed_345_fraction

end NSHelicalHighBranchBarrier
