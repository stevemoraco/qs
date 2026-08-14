import Mathlib

/-!
# RG accumulated-remainder theorem

This file closes a finite but load-bearing part of the dimensional-transmutation
normalization problem.

Suppose a weak-coupling RG trajectory `u n` grows at least quadratically,

    beta * (u n)^2 <= u (n+1) - u n,

and a corrected inverse-coupling coordinate `phi n` has one-step defect

    |(phi (n+1) - phi n) + 1| <= K * (u n)^2.

Then the total defect up to any crossing index `N` is not of logarithmic size.
It is bounded by the *finite coupling budget*

    (K / beta) * (u N - u 0).

Consequently, if the trajectory is stopped at a fixed weak-coupling threshold
`u N <= U`, the corrected crossing-time remainder is uniformly O(1):

    |phi N - phi 0 + N| <= (K / beta) * U.

This is the finite summability mechanism needed after extracting the universal
logarithmic counterterm from a two-loop RG recurrence.  It shows that local
`O(u^2)` corrected-coordinate errors accumulate to `O(1)` because every RG
step consumes at least a quadratic amount of coupling growth.

Honesty boundary: this file does not prove that a Yang--Mills blocking map has
the required one-step `O(u^2)` corrected defect, does not identify recurrence
coefficients with a specific renormalization scheme, and does not prove a mass
gap or Osterwalder--Schrader reconstruction.
-/

namespace Millennium.YangMills

/-- Forward differences telescope over a finite RG trajectory. -/
theorem sum_range_forward_differences
    (u : ℕ → ℝ) (N : ℕ) :
    (∑ n in Finset.range N, (u (n + 1) - u n)) = u N - u 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- A constant multiple of forward differences telescopes as well. -/
theorem sum_range_scaled_forward_differences
    (u : ℕ → ℝ) (a : ℝ) (N : ℕ) :
    (∑ n in Finset.range N, a * (u (n + 1) - u n)) =
      a * (u N - u 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Triangle inequality for an arbitrary finite range sum, proved here by
induction so the later result does not depend on a specialized sum lemma. -/
theorem abs_sum_range_le_sum_abs
    (f : ℕ → ℝ) (N : ℕ) :
    |∑ n in Finset.range N, f n| ≤ ∑ n in Finset.range N, |f n| := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact le_trans (abs_add _ _) (add_le_add ih (le_refl _))

/-- Quadratic RG growth converts a local `K u^2` defect into a finite endpoint
budget.  This is the key summability estimate. -/
theorem quadratic_growth_defect_budget
    (u err : ℕ → ℝ) (N : ℕ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hlocal : ∀ n < N,
      |err n| ≤ K * (u n)^2) :
    (∑ n in Finset.range N, |err n|) ≤
      (K / beta) * (u N - u 0) := by
  have hcoef : 0 ≤ K / beta :=
    div_nonneg hK (le_of_lt hbeta)
  have hpoint : ∀ n ∈ Finset.range N,
      |err n| ≤ (K / beta) * (u (n + 1) - u n) := by
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    calc
      |err n| ≤ K * (u n)^2 := hlocal n hnlt
      _ = (K / beta) * (beta * (u n)^2) := by
        field_simp [ne_of_gt hbeta]
        <;> ring
      _ ≤ (K / beta) * (u (n + 1) - u n) :=
        mul_le_mul_of_nonneg_left (hgrowth n hnlt) hcoef
  calc
    (∑ n in Finset.range N, |err n|) ≤
        ∑ n in Finset.range N, (K / beta) * (u (n + 1) - u n) :=
      Finset.sum_le_sum hpoint
    _ = (K / beta) * (u N - u 0) :=
      sum_range_scaled_forward_differences u (K / beta) N

/-- One-step residual of a corrected crossing-time coordinate. -/
def correctedResidual (phi : ℕ → ℝ) (n : ℕ) : ℝ :=
  (phi (n + 1) - phi n) + 1

/-- The corrected residuals telescope to the crossing-time remainder. -/
theorem sum_correctedResidual
    (phi : ℕ → ℝ) (N : ℕ) :
    (∑ n in Finset.range N, correctedResidual phi n) =
      phi N - phi 0 + (N : ℝ) := by
  induction N with
  | zero => simp [correctedResidual]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp [correctedResidual, Nat.cast_succ]
      ring

/-- The absolute crossing-time remainder is controlled by the accumulated
absolute one-step residual. -/
theorem corrected_remainder_le_sum_abs
    (phi : ℕ → ℝ) (N : ℕ) :
    |phi N - phi 0 + (N : ℝ)| ≤
      ∑ n in Finset.range N, |correctedResidual phi n| := by
  rw [← sum_correctedResidual phi N]
  exact abs_sum_range_le_sum_abs (correctedResidual phi) N

/-- Main finite RG theorem: a corrected coordinate with local `O(u^2)` defect
has a globally bounded crossing-time remainder whenever the coupling grows at
least quadratically. -/
theorem corrected_remainder_from_quadratic_growth
    (u phi : ℕ → ℝ) (N : ℕ)
    {beta K : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hlocal : ∀ n < N,
      |correctedResidual phi n| ≤ K * (u n)^2) :
    |phi N - phi 0 + (N : ℝ)| ≤
      (K / beta) * (u N - u 0) := by
  exact le_trans
    (corrected_remainder_le_sum_abs phi N)
    (quadratic_growth_defect_budget
      u (correctedResidual phi) N hbeta hK hgrowth hlocal)

/-- If the RG crossing occurs below a fixed threshold `U` and starts at a
nonnegative coupling, the corrected crossing-time error has a regulator-
independent O(1) ceiling. -/
theorem corrected_remainder_uniform_at_fixed_threshold
    (u phi : ℕ → ℝ) (N : ℕ)
    {beta K U : ℝ}
    (hbeta : 0 < beta)
    (hK : 0 ≤ K)
    (hu0 : 0 ≤ u 0)
    (huN : u N ≤ U)
    (hgrowth : ∀ n < N,
      beta * (u n)^2 ≤ u (n + 1) - u n)
    (hlocal : ∀ n < N,
      |correctedResidual phi n| ≤ K * (u n)^2) :
    |phi N - phi 0 + (N : ℝ)| ≤ (K / beta) * U := by
  have hcoef : 0 ≤ K / beta :=
    div_nonneg hK (le_of_lt hbeta)
  have hendpoint : u N - u 0 ≤ U := by
    linarith
  exact le_trans
    (corrected_remainder_from_quadratic_growth
      u phi N hbeta hK hgrowth hlocal)
    (mul_le_mul_of_nonneg_left hendpoint hcoef)

#print axioms sum_range_forward_differences
#print axioms sum_range_scaled_forward_differences
#print axioms abs_sum_range_le_sum_abs
#print axioms quadratic_growth_defect_budget
#print axioms sum_correctedResidual
#print axioms corrected_remainder_le_sum_abs
#print axioms corrected_remainder_from_quadratic_growth
#print axioms corrected_remainder_uniform_at_fixed_threshold

end Millennium.YangMills
