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
explicit nonconstant-tail budget, and chooses one concrete positive radius
whose complete source tail fits inside any prescribed strict margin.

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
    (∑ k ∈ Finset.range n, q ^ (k + 1)) ≤ q / (1 - q) := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have hne : 1 - q ≠ 0 := ne_of_gt hd
  have hid :
      (1 - q) * (∑ k ∈ Finset.range n, q ^ (k + 1)) =
        q - q ^ (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        ring
  have hright : (1 - q) * (q / (1 - q)) = q := by
    field_simp [hne]
  have hp : 0 ≤ q ^ (n + 1) := pow_nonneg hq0 (n + 1)
  nlinarith

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
      (∑ k ∈ Finset.range n, |a (k + 1)| * r ^ (k + 1)) ≤
          ∑ k ∈ Finset.range n, C * (r / rho) ^ (k + 1) := by
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
      _ = C * (∑ k ∈ Finset.range n, (r / rho) ^ (k + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ C * ((r / rho) / (1 - r / rho)) := by
        exact mul_le_mul_of_nonneg_left
          (geometric_tail_partial_le (r / rho) hq0 hq1 n) hC
      _ = C * (r / rho) / (1 - r / rho) := by
        ring

/-- Ratio of the source tube spent to fit a Cauchy tail under margin `delta`. -/
noncomputable def sourceMarginRatio (C delta : ℝ) : ℝ :=
  delta / (2 * (C + delta))

/-- Concrete source radius obtained by spending the margin ratio. -/
noncomputable def sourceMarginRadius (rho C delta : ℝ) : ℝ :=
  rho * sourceMarginRatio C delta

/-- The margin ratio is positive. -/
theorem sourceMarginRatio_pos
    (C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    0 < sourceMarginRatio C delta := by
  unfold sourceMarginRatio
  have hsum : 0 < C + delta := by linarith
  positivity

/-- The margin ratio is strictly smaller than one. -/
theorem sourceMarginRatio_lt_one
    (C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    sourceMarginRatio C delta < 1 := by
  unfold sourceMarginRatio
  have hden : 0 < 2 * (C + delta) := by linarith
  exact (div_lt_one hden).2 (by linarith)

/-- The geometric Cauchy tail at the explicit ratio is strictly below the
prescribed margin. -/
theorem sourceMarginRatio_tail_lt
    (C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    C * sourceMarginRatio C delta /
        (1 - sourceMarginRatio C delta) < delta := by
  have hsum : 0 < C + delta := by linarith
  have htwoc : 0 < 2 * C + delta := by linarith
  have hsumne : C + delta ≠ 0 := ne_of_gt hsum
  have htwocne : 2 * C + delta ≠ 0 := ne_of_gt htwoc
  have hidentity :
      C * sourceMarginRatio C delta /
          (1 - sourceMarginRatio C delta) =
        C * delta / (2 * C + delta) := by
    unfold sourceMarginRatio
    field_simp [hsumne, htwocne]
    <;> ring
  rw [hidentity]
  apply (div_lt_iff₀ htwoc).2
  nlinarith [mul_pos hdelta hdelta, mul_nonneg hC hdelta.le]

/-- The explicit source radius is positive. -/
theorem sourceMarginRadius_pos
    (rho C delta : ℝ)
    (hrho : 0 < rho)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    0 < sourceMarginRadius rho C delta := by
  unfold sourceMarginRadius
  exact mul_pos hrho (sourceMarginRatio_pos C delta hC hdelta)

/-- The explicit source radius stays strictly inside the original tube. -/
theorem sourceMarginRadius_lt_tube
    (rho C delta : ℝ)
    (hrho : 0 < rho)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    sourceMarginRadius rho C delta < rho := by
  unfold sourceMarginRadius
  exact mul_lt_mul_of_pos_left
    (sourceMarginRatio_lt_one C delta hC hdelta) hrho

/-- Dividing the explicit radius by the tube radius recovers the margin ratio. -/
theorem sourceMarginRadius_div_tube
    (rho C delta : ℝ)
    (hrho : 0 < rho) :
    sourceMarginRadius rho C delta / rho = sourceMarginRatio C delta := by
  unfold sourceMarginRadius
  field_simp [ne_of_gt hrho]

/-- One explicit positive source radius makes the complete nonconstant Cauchy
tail smaller than any prescribed positive margin. -/
theorem cauchy_nonconstant_tail_fits_margin
    (a : ℕ → ℝ)
    (C rho delta : ℝ)
    (hC : 0 ≤ C)
    (hrho : 0 < rho)
    (hdelta : 0 < delta)
    (ha : ∀ k : ℕ, |a k| ≤ C / rho ^ k) :
    ∃ r : ℝ,
      0 < r ∧ r < rho ∧
      (∑' k : ℕ, |a (k + 1)| * r ^ (k + 1)) < delta := by
  let r := sourceMarginRadius rho C delta
  have hr : 0 < r := sourceMarginRadius_pos rho C delta hrho hC hdelta
  have hrrho : r < rho :=
    sourceMarginRadius_lt_tube rho C delta hrho hC hdelta
  refine ⟨r, hr, hrrho, ?_⟩
  have hbound := cauchy_nonconstant_tail_tsum_le
    a C r rho hC hr.le hrho hrrho ha
  have hratio : r / rho = sourceMarginRatio C delta := by
    exact sourceMarginRadius_div_tube rho C delta hrho
  have hmargin := sourceMarginRatio_tail_lt C delta hC hdelta
  rw [hratio] at hbound
  exact hbound.trans_lt hmargin

/-- One explicit source radius pays the same strict margin uniformly for an
entire coefficient family sharing one Cauchy estimate. -/
theorem uniform_cauchy_family_tail_fits_margin
    {ι : Type*}
    (a : ι → ℕ → ℝ)
    (C rho delta : ℝ)
    (hC : 0 ≤ C)
    (hrho : 0 < rho)
    (hdelta : 0 < delta)
    (ha : ∀ i : ι, ∀ k : ℕ, |a i k| ≤ C / rho ^ k) :
    ∃ r : ℝ,
      0 < r ∧ r < rho ∧
      ∀ i : ι,
        (∑' k : ℕ, |a i (k + 1)| * r ^ (k + 1)) < delta := by
  let r := sourceMarginRadius rho C delta
  have hr : 0 < r := sourceMarginRadius_pos rho C delta hrho hC hdelta
  have hrrho : r < rho :=
    sourceMarginRadius_lt_tube rho C delta hrho hC hdelta
  refine ⟨r, hr, hrrho, ?_⟩
  intro i
  have hbound := cauchy_nonconstant_tail_tsum_le
    (a i) C r rho hC hr.le hrho hrrho (ha i)
  have hratio : r / rho = sourceMarginRatio C delta := by
    exact sourceMarginRadius_div_tube rho C delta hrho
  have hmargin := sourceMarginRatio_tail_lt C delta hC hdelta
  rw [hratio] at hbound
  exact hbound.trans_lt hmargin

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
#print axioms sourceMarginRatio_pos
#print axioms sourceMarginRatio_lt_one
#print axioms sourceMarginRatio_tail_lt
#print axioms sourceMarginRadius_pos
#print axioms sourceMarginRadius_lt_tube
#print axioms sourceMarginRadius_div_tube
#print axioms cauchy_nonconstant_tail_fits_margin
#print axioms uniform_cauchy_family_tail_fits_margin
#print axioms cauchy_coefficients_have_common_positive_radius
#print axioms uniform_cauchy_family_has_common_positive_radius

end Millennium.YangMills
