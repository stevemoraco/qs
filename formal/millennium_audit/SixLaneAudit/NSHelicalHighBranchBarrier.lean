import Mathlib

namespace Millennium.NavierStokes

/-- Ordered positive triad magnitudes give positive denominators for the high-child fraction. -/
theorem helical_high_child_denominators_positive
    (ell m h : ℝ) (hell : 0 < ell) (helm : ell < m) (hmh : m < h) :
    0 < h ∧ 0 < h - ell := by
  constructor
  · linarith
  · linarith

/-- Exact algebraic gap between inverse frequency gain and the same-helicity high-child energy share. -/
theorem helical_high_child_gap_identity
    (ell m h : ℝ) (hell : 0 < ell) (helm : ell < m) (hmh : m < h) :
    m / h - (m - ell) / (h - ell) = ell * (h - m) / (h * (h - ell)) := by
  have hh : h ≠ 0 := ne_of_gt (by linarith : 0 < h)
  have hhe : h - ell ≠ 0 := ne_of_gt (by linarith : 0 < h - ell)
  field_simp [hh, hhe]
  ring

/-- Every nondegenerate ordered same-helicity triad loses more high-child energy than inverse frequency gain allows. -/
theorem helical_high_child_fraction_lt_inverse_gain
    (ell m h : ℝ) (hell : 0 < ell) (helm : ell < m) (hmh : m < h) :
    (m - ell) / (h - ell) < m / h := by
  have hh : 0 < h := by linarith
  have hhe : 0 < h - ell := by linarith
  apply (div_lt_div_iff₀ hhe hh).2
  nlinarith

/-- On the exact growing branch `c*y^2=b*z^2`, the high-child energy share is `c/(b+c)`. -/
theorem helical_growing_branch_energy_fraction
    (b c y z : ℝ)
    (hb : 0 < b) (hc : 0 < c)
    (hpair : 0 < y ^ 2 + z ^ 2)
    (hinv : c * y ^ 2 = b * z ^ 2) :
    z ^ 2 / (y ^ 2 + z ^ 2) = c / (b + c) := by
  have hbc : b + c ≠ 0 := ne_of_gt (by linarith : 0 < b + c)
  have hp : y ^ 2 + z ^ 2 ≠ 0 := ne_of_gt hpair
  field_simp [hbc, hp]
  nlinarith [hinv]

/-- Specialization of the growing-branch share to an ordered same-helicity triad. -/
theorem helical_high_child_exact_fraction
    (ell m h y z : ℝ)
    (hell : 0 < ell) (helm : ell < m) (hmh : m < h)
    (hpair : 0 < y ^ 2 + z ^ 2)
    (hinv : (m - ell) * y ^ 2 = (h - m) * z ^ 2) :
    z ^ 2 / (y ^ 2 + z ^ 2) = (m - ell) / (h - ell) := by
  have hb : 0 < h - m := by linarith
  have hc : 0 < m - ell := by linarith
  calc
    z ^ 2 / (y ^ 2 + z ^ 2) = (m - ell) / ((h - m) + (m - ell)) :=
      helical_growing_branch_energy_fraction (h - m) (m - ell) y z hb hc hpair hinv
    _ = (m - ell) / (h - ell) := by ring_nf

/-- One exact relay step strictly decreases the weighted quantity `energy * frequency`. -/
theorem helical_one_step_weighted_energy_descent
    (ell m h Rold Rnew : ℝ)
    (hell : 0 < ell) (helm : ell < m) (hmh : m < h)
    (hR : 0 < Rold)
    (htransfer : Rnew ^ 2 = ((m - ell) / (h - ell)) * Rold ^ 2) :
    Rnew ^ 2 * h < Rold ^ 2 * m := by
  have hh : 0 < h := by linarith
  have hfrac := helical_high_child_fraction_lt_inverse_gain ell m h hell helm hmh
  have hscaled : ((m - ell) / (h - ell)) * h < m := by
    calc
      ((m - ell) / (h - ell)) * h < (m / h) * h :=
        (mul_lt_mul_right hh).2 hfrac
      _ = m := by
        field_simp [ne_of_gt hh]
  have hR2 : 0 < Rold ^ 2 := sq_pos_of_pos hR
  calc
    Rnew ^ 2 * h = (((m - ell) / (h - ell)) * Rold ^ 2) * h := by rw [htransfer]
    _ = (((m - ell) / (h - ell)) * h) * Rold ^ 2 := by ring
    _ < m * Rold ^ 2 := (mul_lt_mul_right hR2).2 hscaled
    _ = Rold ^ 2 * m := by ring

#print axioms helical_high_child_gap_identity
#print axioms helical_high_child_fraction_lt_inverse_gain
#print axioms helical_growing_branch_energy_fraction
#print axioms helical_high_child_exact_fraction
#print axioms helical_one_step_weighted_energy_descent

end Millennium.NavierStokes
