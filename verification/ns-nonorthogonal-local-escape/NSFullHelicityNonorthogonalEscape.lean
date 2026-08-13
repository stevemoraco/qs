import Mathlib

/-!
# Nonorthogonal full-helicity local escape

This file formalizes the scalar algebra behind the nonorthogonal escape from the
orthogonal retention/gain barrier.

For normalized squared low-to-pump ratio `x=L²/M²` and gain `g=H/M`, the
helicity-complete local high-child fraction is

  f = (1-x)(g²+1) / (2(g²-x)).

The key factorization gives an exact criterion for `f*g>1`.  The integer cell

  p=(1,1,0), q=(8,0,0), r=(9,1,0)

has `L²=2`, `M²=64`, `H²=82`, corrected fraction `2263/2560`, and an exact
positive squared-margin certificate.

No Fourier-analysis, recursive-chain, or PDE conclusion is encoded here.
-/

namespace NSFullHelicityNonorthogonalEscape

/-- Cross-multiplied factorization controlling the sign of `f*g-1`. -/
theorem retention_gain_factorization (x g : ℝ) :
    g * (1 - x) * (g ^ 2 + 1) - 2 * (g ^ 2 - x) =
      -(g - 1) * (x * g ^ 2 + x * g + 2 * x - g ^ 2 + g) := by
  ring

/-- Exact criterion sufficient for the nonorthogonal local retention/gain
product to exceed one. -/
theorem retention_gain_gt_one
    {x g : ℝ}
    (hg : 1 < g)
    (hxg : x < g ^ 2)
    (hshape : x * (g ^ 2 + g + 2) < g * (g - 1)) :
    1 < ((1 - x) * (g ^ 2 + 1) / (2 * (g ^ 2 - x))) * g := by
  have hden : 0 < 2 * (g ^ 2 - x) := by linarith
  have hP : x * g ^ 2 + x * g + 2 * x - g ^ 2 + g < 0 := by
    nlinarith [hshape]
  have hneg : -(g - 1) < 0 := by linarith
  have hprod : 0 < -(g - 1) *
      (x * g ^ 2 + x * g + 2 * x - g ^ 2 + g) :=
    mul_pos_of_neg_of_neg hneg hP
  have hcross : 2 * (g ^ 2 - x) <
      g * (1 - x) * (g ^ 2 + 1) := by
    nlinarith [retention_gain_factorization x g]
  have hre :
      ((1 - x) * (g ^ 2 + 1) / (2 * (g ^ 2 - x))) * g =
        (g * (1 - x) * (g ^ 2 + 1)) / (2 * (g ^ 2 - x)) := by
    ring
  rw [hre]
  exact (lt_div_iff₀ hden).2 hcross

/-- The exact positive local sideband eigenvalue for the integer cell. -/
theorem integer_cell_positive_eigenvalue :
    ((1 : ℝ) / 2) * ((82 : ℝ) - 64) * (64 - 2) /
        (2 * 82) = (279 : ℝ) / 82 := by
  norm_num

/-- The exact negative local sideband eigenvalue for the integer cell. -/
theorem integer_cell_negative_eigenvalue :
    -((2 : ℝ) * ((1 : ℝ) / 2) / 2) = -(1 : ℝ) / 2 := by
  norm_num

/-- The corrected high-child energy fraction for the integer cell. -/
theorem integer_cell_fraction :
    (((64 : ℝ) - 2) * (82 + 64)) /
        (2 * 64 * (82 - 2)) = (2263 : ℝ) / 2560 := by
  norm_num

/-- Exact integer certificate behind the squared retention/gain margin. -/
theorem integer_cell_margin :
    (0 : ℤ) < 82 * 2263 ^ 2 - 64 * 2560 ^ 2 := by
  norm_num

/-- Rational squared form of the exact local escape. -/
theorem integer_cell_squared_escape :
    (1 : ℝ) < ((2263 : ℝ) / 2560) ^ 2 * ((82 : ℝ) / 64) := by
  norm_num

/-- A positive product whose square exceeds one itself exceeds one. -/
theorem positive_of_square_gt_one
    {y : ℝ}
    (hy : 0 < y)
    (hsq : 1 < y ^ 2) :
    1 < y := by
  by_contra hnot
  have hle : y ≤ 1 := le_of_not_gt hnot
  nlinarith

/-- Exact local escape for any positive gain with squared value `82/64`; in
particular this applies to `sqrt(82)/8`. -/
theorem integer_cell_retention_gain_escape
    {G : ℝ}
    (hG : 0 < G)
    (hGsq : G ^ 2 = (82 : ℝ) / 64) :
    1 < ((2263 : ℝ) / 2560) * G := by
  have hf : 0 < (2263 : ℝ) / 2560 := by norm_num
  have hy : 0 < ((2263 : ℝ) / 2560) * G := mul_pos hf hG
  have hsq : 1 < (((2263 : ℝ) / 2560) * G) ^ 2 := by
    calc
      (1 : ℝ) < ((2263 : ℝ) / 2560) ^ 2 * ((82 : ℝ) / 64) :=
        integer_cell_squared_escape
      _ = (((2263 : ℝ) / 2560) * G) ^ 2 := by
        rw [← hGsq]
        ring
  exact positive_of_square_gt_one hy hsq

/-- Exact algebraic identity for the corrected general fraction. -/
theorem fraction_normalization
    {L2 M2 H2 : ℝ}
    (hM : M2 ≠ 0)
    (hHM : H2 - L2 ≠ 0) :
    ((M2 - L2) * (H2 + M2)) / (2 * M2 * (H2 - L2)) =
      ((1 - L2 / M2) * (H2 / M2 + 1)) /
        (2 * (H2 / M2 - L2 / M2)) := by
  field_simp
  ring

#print axioms retention_gain_factorization
#print axioms retention_gain_gt_one
#print axioms integer_cell_positive_eigenvalue
#print axioms integer_cell_negative_eigenvalue
#print axioms integer_cell_fraction
#print axioms integer_cell_margin
#print axioms integer_cell_squared_escape
#print axioms positive_of_square_gt_one
#print axioms integer_cell_retention_gain_escape
#print axioms fraction_normalization

end NSFullHelicityNonorthogonalEscape
