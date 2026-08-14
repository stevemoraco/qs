import Mathlib

noncomputable section

/-!
# Navier--Stokes: Yu far-field forward-growth convolution gate

Runlong Yu's reassigned far-field estimate (arXiv:2606.27560v1,
Proposition 8.6 / Theorem 8.7) contains the one-sided dyadic kernel
`2^{-(k-j)}` multiplying an annular source amplitude and a finer-scale
local-enstrophy quantity.

This finite file isolates a second route to closure besides separate
`ell^p`/`ell^q` control.

If the finer-scale quantity grows forward by at most `c^m` over `m` dyadic
steps, then the reassignment kernel sees the geometric factor `(c/2)^m`.
Thus every finite reassigned row has a uniform bound whenever `c < 2`.
At the critical growth rate `c = 2`, the dyadic kernel is cancelled exactly;
a row accumulates linearly even though the model diagonal product
`A_j Q_j = 2^{-j}` has a uniformly bounded partial-sum budget.

This is finite scalar/sequence algebra only.  It does not prove that Yu's
annular quantities for a Navier--Stokes solution satisfy any forward-growth
hypothesis, nor does it prove regularity or blow-up.
-/

namespace NSYuForwardGrowthConvolutionGate

open scoped BigOperators

/-- Exact finite geometric-series identity, written in a form that avoids any
infinite-series machinery. -/
theorem geometric_partial_sum_identity (x : ℝ) (n : ℕ) :
    (1 - x) * (∑ m ∈ Finset.range n, x ^ m) = 1 - x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (1 - x) * ((∑ m ∈ Finset.range n, x ^ m) + x ^ n) =
            (1 - x) * (∑ m ∈ Finset.range n, x ^ m) +
              (1 - x) * x ^ n := by ring
        _ = (1 - x ^ n) + (1 - x) * x ^ n := by rw [ih]
        _ = 1 - x ^ n * x := by ring

/-- Every finite geometric row is uniformly bounded when the ratio is strictly
below one. -/
theorem geometric_partial_sum_le_inverse_gap
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (∑ m ∈ Finset.range n, x ^ m) ≤ 1 / (1 - x) := by
  have hgap : 0 < 1 - x := by linarith
  have hpow : 0 ≤ x ^ n := pow_nonneg hx0 n
  have hid := geometric_partial_sum_identity x n
  apply (le_div_iff₀ hgap).2
  nlinarith

/-- If a finer-scale reservoir grows by at most a factor `c` per dyadic step,
then Yu's `2^{-m}` reassignment kernel has a uniform finite row budget whenever
`c < 2`. -/
theorem dyadic_forward_growth_kernel_bound
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c < 2) (n : ℕ) :
    (∑ m ∈ Finset.range n, (c / 2) ^ m) ≤ 2 / (2 - c) := by
  have hx0 : 0 ≤ c / 2 := by positivity
  have hx1 : c / 2 < 1 := by linarith
  calc
    (∑ m ∈ Finset.range n, (c / 2) ^ m) ≤ 1 / (1 - c / 2) :=
      geometric_partial_sum_le_inverse_gap hx0 hx1 n
    _ = 2 / (2 - c) := by
      have hden : 2 - c ≠ 0 := by linarith
      field_simp [hden]
      ring

/-- One lag of the reassigned far-field row.  The source-shaped kernel
`2^{-m}` converts forward growth `c^m` into the effective ratio `(c/2)^m`. -/
theorem one_lag_forward_growth_bound
    {A Q0 Qm D c : ℝ} {m : ℕ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hQ0 : 0 ≤ Q0)
    (hQm : Qm ≤ D * c ^ m * Q0) :
    (1 / 2 : ℝ) ^ m * A * Qm ≤
      D * A * Q0 * (c / 2) ^ m := by
  have hfac : 0 ≤ (1 / 2 : ℝ) ^ m * A := by positivity
  have h := mul_le_mul_of_nonneg_left hQm hfac
  have hpow : (1 / 2 : ℝ) ^ m * c ^ m = (c / 2) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (1 / 2 : ℝ) ^ m * A * Qm ≤
        ((1 / 2 : ℝ) ^ m * A) * (D * c ^ m * Q0) := h
    _ = D * A * Q0 * ((1 / 2 : ℝ) ^ m * c ^ m) := by ring
    _ = D * A * Q0 * (c / 2) ^ m := by rw [hpow]

/-- Finite row version of the forward-growth closure.  This is the reusable
inequality: under `Q_m ≤ D c^m Q_0` with `c < 2`, the complete Yu-shaped
reassignment row costs at most `2D/(2-c)` times the diagonal product `A Q_0`. -/
theorem finite_reassigned_row_closure
    (Q : ℕ → ℝ) {A Q0 D c : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (hQ0 : 0 ≤ Q0) (hD : 0 ≤ D)
    (hc0 : 0 ≤ c) (hc2 : c < 2)
    (hgrowth : ∀ m < n, Q m ≤ D * c ^ m * Q0) :
    (∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m * A * Q m) ≤
      D * A * Q0 * (2 / (2 - c)) := by
  have hcoef : 0 ≤ D * A * Q0 := by positivity
  calc
    (∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m * A * Q m) ≤
        ∑ m ∈ Finset.range n, D * A * Q0 * (c / 2) ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      exact one_lag_forward_growth_bound hA hD hQ0
        (hgrowth m (Finset.mem_range.mp hm))
    _ = D * A * Q0 * (∑ m ∈ Finset.range n, (c / 2) ^ m) := by
      rw [Finset.mul_sum]
    _ ≤ D * A * Q0 * (2 / (2 - c)) := by
      exact mul_le_mul_of_nonneg_left
        (dyadic_forward_growth_kernel_bound hc0 hc2 n) hcoef

/-- At the critical forward-growth rate `c = 2`, the reassignment kernel is
cancelled exactly at every lag. -/
theorem critical_growth_cancels_dyadic_kernel (m : ℕ) :
    (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
  rw [← mul_pow]
  norm_num

/-- Consequently the critical reassignment row grows exactly linearly with the
number of visible lags. -/
theorem critical_growth_row_is_linear (n : ℕ) :
    (∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m) = n := by
  simp [critical_growth_cancels_dyadic_kernel]

/-- In the explicit critical model `A_j=4^{-j}`, `Q_j=2^j`, the diagonal
product is nevertheless the summable geometric profile `2^{-j}`. -/
theorem critical_model_diagonal_product (j : ℕ) :
    (1 / 4 : ℝ) ^ j * (2 : ℝ) ^ j = (1 / 2 : ℝ) ^ j := by
  rw [← mul_pow]
  congr 1
  norm_num

/-- The critical model therefore has a uniformly bounded diagonal-product
budget even though its forward reassignment row is linearly divergent. -/
theorem critical_model_diagonal_budget (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j * (2 : ℝ) ^ j) ≤ 2 := by
  calc
    (∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j * (2 : ℝ) ^ j) =
        ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro j _
      exact critical_model_diagonal_product j
    _ ≤ 1 / (1 - (1 / 2 : ℝ)) := by
      exact geometric_partial_sum_le_inverse_gap (by norm_num) (by norm_num) n
    _ = 2 := by norm_num

#print axioms geometric_partial_sum_identity
#print axioms geometric_partial_sum_le_inverse_gap
#print axioms dyadic_forward_growth_kernel_bound
#print axioms one_lag_forward_growth_bound
#print axioms finite_reassigned_row_closure
#print axioms critical_growth_cancels_dyadic_kernel
#print axioms critical_growth_row_is_linear
#print axioms critical_model_diagonal_product
#print axioms critical_model_diagonal_budget

end NSYuForwardGrowthConvolutionGate
