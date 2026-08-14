import Mathlib

open scoped BigOperators

namespace Millennium.YangMills

/-!
# Cauchy coefficient bounds give one common positive source radius

The manuscript's marked coefficient norm already divides the order-`k`
derivative by `k!`. Thus a Cauchy estimate on one source tube has the form

  |a k| <= C / rho^k

for the normalized coefficients. This file proves that every strictly smaller
radius gives an absolutely summable weighted coefficient series, gives an
explicit nonconstant-tail budget, and exhibits the half-radius as one common
positive radius.

This is real infinite-series algebra. It does not instantiate Kirk's polymer
coefficients or prove Yang--Mills, a mass gap, or a Clay theorem.
-/

/-- A normalized Cauchy coefficient bound is absolutely summable at every
strictly smaller nonnegative radius. -/
theorem cauchy_coefficients_summable_at_smaller_radius
    (a : ℕ → ℝ)
    (C r rho : ℝ)
    (hr : 0 ≤ r)
    (hrho : 0 < rho)
    (hrrho : r < rho)
    (ha : ∀ k : ℕ, |a k| ≤ C / rho ^ k) :
    Summable (fun k : ℕ => |a k| * r ^ k) := by
  have hq0 : 0 ≤ r / rho := div_nonneg hr hrho.le
  have hqnorm : ‖r / rho‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact (div_lt_one hrho).2 hrrho
  have hgeom : Summable (fun k : ℕ => (r / rho) ^ k) :=
    summable_geometric_of_norm_lt_one hqnorm
  have hmajor : Summable (fun k : ℕ => C * (r / rho) ^ k) :=
    hgeom.mul_left C
  have hnonneg : ∀ k : ℕ, 0 ≤ |a k| * r ^ k := by
    intro k
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hr k)
  have hdom : ∀ k : ℕ, |a k| * r ^ k ≤ C * (r / rho) ^ k := by
    intro k
    have hmul := mul_le_mul_of_nonneg_right (ha k) (pow_nonneg hr k)
    calc
      |a k| * r ^ k ≤ (C / rho ^ k) * r ^ k := hmul
      _ = C * (r / rho) ^ k := by
        rw [div_pow]
        ring
  exact .of_nonneg_of_le hnonneg hdom hmajor

/-- A finite geometric tail is bounded by the corresponding infinite-tail
formula. -/
theorem geometric_tail_partial_le
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (n : ℕ) :
    (∑ k in Finset.range n, q ^ (k + 1)) ≤ q / (1 - q) := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have hne : 1 - q ≠ 0 := ne_of_gt hd
  have hid :
      (1 - q) * (∑ k in Finset.range n, q ^ (k + 1)) =
        q - q ^ (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        ring
  apply (mul_le_mul_left hd).mp
  rw [hid]
  have hright : (1 - q) * (q / (1 - q)) = q := by
    field_simp [hne]
  rw [hright]
  exact sub_le_self q (pow_nonneg hq0 (n + 1))

/-- Explicit bound on the nonconstant weighted source tail. -/
theorem cauchy_nonconstant_tail_tsum_le
    (a : ℕ → ℝ)
    (C r rho : ℝ)
    (hC : 0 ≤ C)
    (hr : 0 ≤ r)
    (hrho : 0 < rho)
    (hrrho : r < rho)
    (ha : ∀ k : ℕ, |a k| ≤ C / rho ^ k) :
    (∑' k : ℕ, |a (k + 1)| * r ^ (k + 1)) ≤
      C * (r / rho) / (1 - r / rho) := by
  have hq0 : 0 ≤ r / rho := div_nonneg hr hrho.le
  have hq1 : r / rho < 1 := (div_lt_one hrho).2 hrrho
  apply Real.tsum_le_of_sum_range_le
  · intro k
    exact mul_nonneg (abs_nonneg _) (pow_nonneg hr (k + 1))
  · intro n
    calc
      (∑ k in Finset.range n, |a (k + 1)| * r ^ (k + 1)) ≤
          ∑ k in Finset.range n, C * (r / rho) ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro k _hk
        have hmul := mul_le_mul_of_nonneg_right
          (ha (k + 1)) (pow_nonneg hr (k + 1))
        calc
          |a (k + 1)| * r ^ (k + 1) ≤
              (C / rho ^ (k + 1)) * r ^ (k + 1) := hmul
          _ = C * (r / rho) ^ (k + 1) := by
            rw [div_pow]
            ring
      _ = C * (∑ k in Finset.range n, (r / rho) ^ (k + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ C * ((r / rho) / (1 - r / rho)) := by
        exact mul_le_mul_of_nonneg_left
          (geometric_tail_partial_le (r / rho) hq0 hq1 n) hC
      _ = C * (r / rho) / (1 - r / rho) := by
        ring

/-- The half-radius is a concrete common positive source radius. -/
theorem cauchy_coefficients_have_common_positive_radius
    (a : ℕ → ℝ)
    (C rho : ℝ)
    (hrho : 0 < rho)
    (ha : ∀ k : ℕ, |a k| ≤ C / rho ^ k) :
    ∃ r : ℝ,
      0 < r ∧ r < rho ∧
      Summable (fun k : ℕ => |a k| * r ^ k) := by
  refine ⟨rho / 2, by linarith, by linarith, ?_⟩
  exact cauchy_coefficients_summable_at_smaller_radius
    a C (rho / 2) rho (by linarith) hrho (by linarith) ha

/-- A family sharing one Cauchy constant and one tube radius has one uniform
positive source radius. -/
theorem uniform_cauchy_family_has_common_positive_radius
    {ι : Type*}
    (a : ι → ℕ → ℝ)
    (C rho : ℝ)
    (hrho : 0 < rho)
    (ha : ∀ i : ι, ∀ k : ℕ, |a i k| ≤ C / rho ^ k) :
    ∃ r : ℝ,
      0 < r ∧ r < rho ∧
      ∀ i : ι, Summable (fun k : ℕ => |a i k| * r ^ k) := by
  refine ⟨rho / 2, by linarith, by linarith, ?_⟩
  intro i
  exact cauchy_coefficients_summable_at_smaller_radius
    (a i) C (rho / 2) rho (by linarith) hrho (by linarith) (ha i)

#print axioms cauchy_coefficients_summable_at_smaller_radius
#print axioms geometric_tail_partial_le
#print axioms cauchy_nonconstant_tail_tsum_le
#print axioms cauchy_coefficients_have_common_positive_radius
#print axioms uniform_cauchy_family_has_common_positive_radius

end Millennium.YangMills
