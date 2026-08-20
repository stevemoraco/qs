import Mathlib

/-!
# Faizal–Shabir long off-diagonal rooted-row firewall

Finite real quadratic-form algebra only. This file does **not** formalize the
Yang–Mills connected-correlation matrix, a localized observable frame, the OS
Hilbert space, regulator/volume uniformity, the mass gap, AF/IR identification,
or the Clay theorem.

The source-facing idea is that a relation-selected mixed/off-diagonal Gram
piece need not be positive. A rooted absolute row/column estimate is enough to
control its harmful quadratic form:

  sum_j |B_ij| <= eps d_i,
  sum_i |B_ij| <= eps d_j

imply

  |sum_ij B_ij x_i x_j| <= eps sum_i d_i x_i^2.

For a symmetric matrix the row and column budgets are the same source theorem.
-/

namespace Millennium.YangMills.FaizalShabirLongOffdiagRootRowFirewall

open scoped BigOperators

/-- One bilinear term is paid by the arithmetic mean of the two diagonal
quadratic weights. -/
theorem abs_bilinear_term_le_half_sq_sum (b x y : ℝ) :
    |b * x * y| <= |b| * (x ^ 2 + y ^ 2) / 2 := by
  have hs : 0 <= (|x| - |y|) ^ 2 := sq_nonneg (|x| - |y|)
  have hxy : |x| * |y| <= (x ^ 2 + y ^ 2) / 2 := by
    rw [← sq_abs x, ← sq_abs y]
    nlinarith
  have hb := mul_le_mul_of_nonneg_left hxy (abs_nonneg b)
  simpa [abs_mul, mul_assoc] using hb

/-- A two-sided rooted absolute row budget controls the entire relation-selected
quadratic form. In the symmetric source application the column budget follows
from the same row estimate. -/
theorem row_col_budget_controls_quadratic_form
    {ι : Type*} [Fintype ι]
    (B : ι -> ι -> ℝ) (d x : ι -> ℝ) (eps : ℝ)
    (heps : 0 <= eps)
    (hd : forall i, 0 <= d i)
    (hrow : forall i, (∑ j, |B i j|) <= eps * d i)
    (hcol : forall j, (∑ i, |B i j|) <= eps * d j) :
    |∑ i, ∑ j, B i j * x i * x j| <=
      eps * ∑ i, d i * x i ^ 2 := by
  classical
  have habs :
      |∑ i, ∑ j, B i j * x i * x j| <=
        ∑ i, ∑ j, |B i j * x i * x j| := by
    calc
      |∑ i, ∑ j, B i j * x i * x j| <=
          ∑ i, |∑ j, B i j * x i * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ i, ∑ j, |B i j * x i * x j| := by
        exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
  have hpair :
      (∑ i, ∑ j, |B i j * x i * x j|) <=
        ∑ i, ∑ j, |B i j| * (x i ^ 2 + x j ^ 2) / 2 := by
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ =>
        abs_bilinear_term_le_half_sq_sum (B i j) (x i) (x j)
  have hA :
      (∑ i, ∑ j, |B i j| * x i ^ 2) <=
        eps * ∑ i, d i * x i ^ 2 := by
    calc
      (∑ i, ∑ j, |B i j| * x i ^ 2)
          = ∑ i, x i ^ 2 * (∑ j, |B i j|) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      _ <= ∑ i, x i ^ 2 * (eps * d i) := by
              exact Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (x i))
      _ = eps * ∑ i, d i * x i ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
  have hB :
      (∑ i, ∑ j, |B i j| * x j ^ 2) <=
        eps * ∑ i, d i * x i ^ 2 := by
    calc
      (∑ i, ∑ j, |B i j| * x j ^ 2)
          = ∑ j, ∑ i, |B i j| * x j ^ 2 := by
              rw [Finset.sum_comm]
      _ = ∑ j, x j ^ 2 * (∑ i, |B i j|) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      _ <= ∑ j, x j ^ 2 * (eps * d j) := by
              exact Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg (x j))
      _ = eps * ∑ j, d j * x j ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
  have hsplit :
      (∑ i, ∑ j, |B i j| * (x i ^ 2 + x j ^ 2) / 2) =
        ((∑ i, ∑ j, |B i j| * x i ^ 2) +
         (∑ i, ∑ j, |B i j| * x j ^ 2)) / 2 := by
    simp [Finset.sum_add_distrib]
    ring
  rw [hsplit] at hpair
  calc
    |∑ i, ∑ j, B i j * x i * x j|
        <= ∑ i, ∑ j, |B i j * x i * x j| := habs
    _ <= ((∑ i, ∑ j, |B i j| * x i ^ 2) +
          (∑ i, ∑ j, |B i j| * x j ^ 2)) / 2 := hpair
    _ <= eps * ∑ i, d i * x i ^ 2 := by linarith

/-- The mixed subtraction can therefore be charged only by its rooted relative
row budget. -/
theorem harmful_subtraction_le_root_budget
    {q d eps : ℝ}
    (habs : |q| <= eps * d) :
    -q <= eps * d := by
  exact le_trans (neg_le_abs q) habs

#print axioms abs_bilinear_term_le_half_sq_sum
#print axioms row_col_budget_controls_quadratic_form
#print axioms harmful_subtraction_le_root_budget

end Millennium.YangMills.FaizalShabirLongOffdiagRootRowFirewall
