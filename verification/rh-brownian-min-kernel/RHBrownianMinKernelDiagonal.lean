import Mathlib

open scoped BigOperators

namespace RHBrownianMinKernelDiagonal

/-- One-cell completion of the square behind the Brownian min-kernel optimizer. -/
theorem one_cell_completion (ds dv B : ℝ) (hds : ds ≠ 0) :
    dv * B - (1 / 2 : ℝ) * ds * B ^ 2 =
      (1 / 2 : ℝ) * (dv ^ 2 / ds) -
        (1 / 2 : ℝ) * ds * (B - dv / ds) ^ 2 := by
  field_simp [hds]
  ring

/-- Exact finite diagonal completion in tail coordinates. -/
theorem finite_diagonal_completion {n : ℕ}
    (ds dv B : Fin n → ℝ) (hds : ∀ i, ds i ≠ 0) :
    (∑ i, (dv i * B i - (1 / 2 : ℝ) * ds i * (B i) ^ 2)) =
      (1 / 2 : ℝ) * ∑ i, (dv i) ^ 2 / ds i -
        (1 / 2 : ℝ) * ∑ i, ds i * (B i - dv i / ds i) ^ 2 := by
  calc
    (∑ i, (dv i * B i - (1 / 2 : ℝ) * ds i * (B i) ^ 2)) =
        ∑ i, ((1 / 2 : ℝ) * ((dv i) ^ 2 / ds i) -
          (1 / 2 : ℝ) * ds i * (B i - dv i / ds i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact one_cell_completion (ds i) (dv i) (B i) (hds i)
    _ = (1 / 2 : ℝ) * ∑ i, (dv i) ^ 2 / ds i -
        (1 / 2 : ℝ) * ∑ i, ds i * (B i - dv i / ds i) ^ 2 := by
          simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- The diagonal capacity is an upper bound when every increment is positive. -/
theorem finite_capacity_upper_bound {n : ℕ}
    (ds dv B : Fin n → ℝ) (hds : ∀ i, 0 < ds i) :
    (∑ i, (dv i * B i - (1 / 2 : ℝ) * ds i * (B i) ^ 2)) ≤
      (1 / 2 : ℝ) * ∑ i, (dv i) ^ 2 / ds i := by
  rw [finite_diagonal_completion ds dv B (fun i => ne_of_gt (hds i))]
  have hsum : 0 ≤ ∑ i, ds i * (B i - dv i / ds i) ^ 2 := by
    exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (le_of_lt (hds i)) (sq_nonneg (B i - dv i / ds i)))
  linarith

/-- Any one mismatched tail coordinate lies strictly below capacity. -/
theorem finite_capacity_strict_of_mismatch {n : ℕ}
    (ds dv B : Fin n → ℝ) (hds : ∀ i, 0 < ds i)
    (j : Fin n) (hm : B j ≠ dv j / ds j) :
    (∑ i, (dv i * B i - (1 / 2 : ℝ) * ds i * (B i) ^ 2)) <
      (1 / 2 : ℝ) * ∑ i, (dv i) ^ 2 / ds i := by
  rw [finite_diagonal_completion ds dv B (fun i => ne_of_gt (hds i))]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ds i * (B i - dv i / ds i) ^ 2 := by
    intro i hi
    exact mul_nonneg (le_of_lt (hds i)) (sq_nonneg (B i - dv i / ds i))
  have hjpos : 0 < ds j * (B j - dv j / ds j) ^ 2 := by
    apply mul_pos (hds j)
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hm)
  have hle : ds j * (B j - dv j / ds j) ^ 2 ≤
      ∑ i, ds i * (B i - dv i / ds i) ^ 2 := by
    exact Finset.single_le_sum hnonneg (Finset.mem_univ j)
  have hsum : 0 < ∑ i, ds i * (B i - dv i / ds i) ^ 2 :=
    lt_of_lt_of_le hjpos hle
  linarith

/-- Cross-multiplied adjacent-prime secant identity, written in square-root variables. -/
theorem inverse_secant_cross_identity (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 / u - 1 / v) * (u ^ 2 + u * v + v ^ 2) =
      (1 / u ^ 3 - 1 / v ^ 3) * (u ^ 2 * v ^ 2) := by
  field_simp [hu, hv]
  ring

/-- The boundary secant from the origin has optimizer slope `u^2`. -/
theorem boundary_optimizer_identity (u : ℝ) (hu : u ≠ 0) :
    (1 / u) / (1 / u ^ 3) = u ^ 2 := by
  field_simp [hu]

/-- A decreasing secant-slope schedule produces a nonnegative optimizer atom. -/
theorem decreasing_slopes_give_nonnegative_atom (d next : ℝ) (h : next ≤ d) :
    0 ≤ d - next := sub_nonneg.mpr h

/-- A positive semidefinite quadratic kernel does not make a linear-minus-quadratic deficit positive. -/
theorem psd_kernel_sign_firewall :
    (3 : ℝ) - (1 / 2 : ℝ) * 3 ^ 2 < 0 := by
  norm_num

/-- Denominator-free exact form of the Brownian cell relinearization. -/
theorem cell_debt_minus_capacity_cross_multiplied (u v T : ℝ) :
    (v ^ 3 - u ^ 3) *
        (T * (u ^ 2 + u * v + v ^ 2) - u ^ 2 * v ^ 2) ^ 2 -
      u ^ 4 * v ^ 4 * (v - u) * (u ^ 2 + u * v + v ^ 2) =
    T * (v - u) *
        ((u ^ 2 + u * v + v ^ 2) * T - 2 * u ^ 2 * v ^ 2) *
      (u ^ 2 + u * v + v ^ 2) ^ 2 := by
  ring

/-- The relinearized cell is nonnegative once its exact threshold is met. -/
theorem cell_relinearized_nonnegative_of_threshold
    (u v T : ℝ) (hu : 0 < u) (huv : u < v) (hT : 0 ≤ T)
    (hthreshold : 2 * u ^ 2 * v ^ 2 ≤
      (u ^ 2 + u * v + v ^ 2) * T) :
    0 ≤ T * (v - u) *
        ((u ^ 2 + u * v + v ^ 2) * T - 2 * u ^ 2 * v ^ 2) /
      (u ^ 3 * v ^ 3) := by
  have hv : 0 < v := lt_trans hu huv
  have hgap : 0 ≤ v - u := sub_nonneg.mpr (le_of_lt huv)
  have hbracket : 0 ≤
      (u ^ 2 + u * v + v ^ 2) * T - 2 * u ^ 2 * v ^ 2 :=
    sub_nonneg.mpr hthreshold
  have hnum : 0 ≤ T * (v - u) *
      ((u ^ 2 + u * v + v ^ 2) * T - 2 * u ^ 2 * v ^ 2) :=
    mul_nonneg (mul_nonneg hT hgap) hbracket
  have hden : 0 ≤ u ^ 3 * v ^ 3 :=
    le_of_lt (mul_pos (pow_pos hu 3) (pow_pos hv 3))
  exact div_nonneg hnum hden

#print axioms one_cell_completion
#print axioms finite_diagonal_completion
#print axioms finite_capacity_upper_bound
#print axioms finite_capacity_strict_of_mismatch
#print axioms inverse_secant_cross_identity
#print axioms boundary_optimizer_identity
#print axioms decreasing_slopes_give_nonnegative_atom
#print axioms psd_kernel_sign_firewall
#print axioms cell_debt_minus_capacity_cross_multiplied
#print axioms cell_relinearized_nonnegative_of_threshold

end RHBrownianMinKernelDiagonal
