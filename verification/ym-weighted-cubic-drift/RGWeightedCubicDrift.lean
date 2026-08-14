import Mathlib

namespace Millennium.YangMills

/-- Forward differences telescope over a finite trajectory. -/
theorem wcd_sum_range_forward_differences
    (u : ℕ → ℝ) (N : ℕ) :
    (∑ n in Finset.range N, (u (n + 1) - u n)) = u N - u 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A constant multiple of forward differences telescopes. -/
theorem wcd_sum_range_scaled_forward_differences
    (u : ℕ → ℝ) (a : ℝ) (N : ℕ) :
    (∑ n in Finset.range N, a * (u (n + 1) - u n)) =
      a * (u N - u 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Triangle inequality for a finite range sum. -/
theorem wcd_abs_sum_range_le_sum_abs
    (f : ℕ → ℝ) (N : ℕ) :
    |∑ n in Finset.range N, f n| ≤ ∑ n in Finset.range N, |f n| := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact le_trans (abs_add_le _ _) (add_le_add ih (le_refl _))

/-- One-step residual of a corrected crossing coordinate. -/
def wcdCorrectedResidual (phi : ℕ → ℝ) (n : ℕ) : ℝ :=
  (phi (n + 1) - phi n) + 1

/-- Corrected residuals telescope to the crossing-time remainder. -/
theorem wcd_sum_correctedResidual
    (phi : ℕ → ℝ) (N : ℕ) :
    (∑ n in Finset.range N, wcdCorrectedResidual phi n) =
      phi N - phi 0 + (N : ℝ) := by
  induction N with
  | zero => simp [wcdCorrectedResidual]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp [wcdCorrectedResidual, Nat.cast_succ]
      ring

/-- Absolute crossing-time remainder is controlled by accumulated residuals. -/
theorem wcd_corrected_remainder_le_sum_abs
    (phi : ℕ → ℝ) (N : ℕ) :
    |phi N - phi 0 + (N : ℝ)| ≤
      ∑ n in Finset.range N, |wcdCorrectedResidual phi n| := by
  rw [← wcd_sum_correctedResidual phi N]
  exact wcd_abs_sum_range_le_sum_abs (wcdCorrectedResidual phi) N

/-- Quadratic local error plus an arbitrary extra error budget accumulates to
an endpoint quadratic budget plus the total extra budget. -/
theorem wcd_corrected_remainder_with_extra_budget
    (u phi extra : ℕ → ℝ) (N : ℕ)
    {beta K W : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hlocal : ∀ n < N,
      |wcdCorrectedResidual phi n| ≤ K * (u n)^2 + extra n)
    (hextra : (∑ n in Finset.range N, extra n) ≤ W) :
    |phi N - phi 0 + (N : ℝ)| ≤
      (K / beta) * (u N - u 0) + W := by
  have hcoef : 0 ≤ K / beta :=
    div_nonneg hK (le_of_lt hbeta)
  have hpoint : ∀ n ∈ Finset.range N,
      |wcdCorrectedResidual phi n| ≤
        (K / beta) * (u (n + 1) - u n) + extra n := by
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    calc
      |wcdCorrectedResidual phi n| ≤ K * (u n)^2 + extra n := hlocal n hnlt
      _ = (K / beta) * (beta * (u n)^2) + extra n := by
        field_simp [ne_of_gt hbeta]
      _ ≤ (K / beta) * (u (n + 1) - u n) + extra n :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left (hgrowth n hnlt) hcoef)
          (extra n)
  calc
    |phi N - phi 0 + (N : ℝ)| ≤
        ∑ n in Finset.range N, |wcdCorrectedResidual phi n| :=
      wcd_corrected_remainder_le_sum_abs phi N
    _ ≤ ∑ n in Finset.range N,
        ((K / beta) * (u (n + 1) - u n) + extra n) :=
      Finset.sum_le_sum hpoint
    _ = (K / beta) * (u N - u 0) +
        ∑ n in Finset.range N, extra n := by
      rw [Finset.sum_add_distrib]
      rw [wcd_sum_range_scaled_forward_differences]
    _ ≤ (K / beta) * (u N - u 0) + W :=
      add_le_add_left hextra _

/-- Fixed-threshold form of the same budget. -/
theorem wcd_corrected_remainder_with_extra_budget_at_threshold
    (u phi extra : ℕ → ℝ) (N : ℕ)
    {beta K W U : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hu0 : 0 ≤ u 0)
    (huN : u N ≤ U)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hlocal : ∀ n < N,
      |wcdCorrectedResidual phi n| ≤ K * (u n)^2 + extra n)
    (hextra : (∑ n in Finset.range N, extra n) ≤ W) :
    |phi N - phi 0 + (N : ℝ)| ≤ (K / beta) * U + W := by
  have hcoef : 0 ≤ K / beta :=
    div_nonneg hK (le_of_lt hbeta)
  have hendpoint : u N - u 0 ≤ U := by
    linarith
  calc
    |phi N - phi 0 + (N : ℝ)| ≤
        (K / beta) * (u N - u 0) + W :=
      wcd_corrected_remainder_with_extra_budget
        u phi extra N hbeta hK hgrowth hlocal hextra
    _ ≤ (K / beta) * U + W :=
      add_le_add_right (mul_le_mul_of_nonneg_left hendpoint hcoef) W

/-- A directly bounded weighted cubic drift is sufficient. -/
theorem wcd_corrected_remainder_from_weighted_cubic_drift
    (u phi delta : ℕ → ℝ) (N : ℕ)
    {beta K W : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hlocal : ∀ n < N,
      |wcdCorrectedResidual phi n| ≤
        K * (u n)^2 + |delta n| * u n)
    (hweighted :
      (∑ n in Finset.range N, |delta n| * u n) ≤ W) :
    |phi N - phi 0 + (N : ℝ)| ≤
      (K / beta) * (u N - u 0) + W := by
  exact wcd_corrected_remainder_with_extra_budget
    u phi (fun n => |delta n| * u n) N
    hbeta hK hgrowth hlocal hweighted

#print axioms wcd_corrected_remainder_with_extra_budget
#print axioms wcd_corrected_remainder_with_extra_budget_at_threshold
#print axioms wcd_corrected_remainder_from_weighted_cubic_drift

end Millennium.YangMills
