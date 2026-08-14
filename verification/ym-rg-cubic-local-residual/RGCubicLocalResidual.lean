import Mathlib

/-!
# Cubic RG local-residual theorem

This file proves the local analytic estimate that complements
`RGAccumulatedRemainder.lean`.

For the exact cubic recurrence

    u' = u * (1 + b*u + c*u^2)

with `b > 0`, `c >= 0`, the corrected inverse-coupling coordinate

    Phi(u) = 1/(b*u) + (c/b^2 - 1) * log u

has a one-step residual of order `u^2` on every fixed weak-coupling interval.
Combined with the accumulated-remainder theorem, this is the finite mechanism
behind an O(1) two-loop crossing-time remainder.

Honesty boundary: this is a scalar exact-cubic model theorem. It does not prove
that a Yang--Mills blocking map is exactly cubic or has a controlled O(u^4)
remainder, and it does not establish scheme matching, a physical mass gap, or
OS reconstruction.
-/

namespace Millennium.YangMills

/-- The logarithmic remainder needed after the two-loop cancellation is
nonnegative for nonnegative `x`. -/
theorem log_one_add_sub_frac_nonneg
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ Real.log (1 + x) - x / (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have hlo := Real.one_sub_inv_le_log_of_pos hpos
  have hid : x / (1 + x) = 1 - (1 + x)⁻¹ := by
    field_simp [ne_of_gt hpos]
    ring
  rw [hid]
  linarith

/-- A coarse but sufficient quadratic upper bound for the logarithmic
remainder. -/
theorem log_one_add_sub_frac_le_sq
    (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) - x / (1 + x) ≤ x^2 := by
  have hpos : 0 < 1 + x := by linarith
  have hlog : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hid : x - x / (1 + x) = x^2 / (1 + x) := by
    field_simp [ne_of_gt hpos]
    ring
  have hfrac : x^2 / (1 + x) ≤ x^2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  calc
    Real.log (1 + x) - x / (1 + x)
        ≤ x - x / (1 + x) := sub_le_sub_right hlog _
    _ = x^2 / (1 + x) := hid
    _ ≤ x^2 := hfrac

/-- Absolute-value form of the logarithmic quadratic remainder. -/
theorem abs_log_one_add_sub_frac_le_sq
    (x : ℝ) (hx : 0 ≤ x) :
    |Real.log (1 + x) - x / (1 + x)| ≤ x^2 := by
  rw [abs_of_nonneg (log_one_add_sub_frac_nonneg x hx)]
  exact log_one_add_sub_frac_le_sq x hx

/-- One exact cubic RG step. -/
def cubicRGStep (b c u : ℝ) : ℝ :=
  u * (1 + b * u + c * u^2)

/-- The two-loop corrected inverse-coupling coordinate for the scalar cubic
recurrence. -/
noncomputable def cubicCorrectedCoordinate (b c u : ℝ) : ℝ :=
  1 / (b * u) + (c / b^2 - 1) * Real.log u

/-- Exact algebraic decomposition of the one-step corrected-coordinate
residual. The first-order term has cancelled. -/
theorem cubic_corrected_residual_identity
    (b c u : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hu : 0 < u) :
    let D := 1 + b * u + c * u^2
    cubicCorrectedCoordinate b c (cubicRGStep b c u)
        - cubicCorrectedCoordinate b c u + 1
      = (c / b^2 - 1) *
          (Real.log D - (D - 1) / D)
        + (c^2 / b^2) * (u^2 / D) := by
  dsimp only
  have hbu : 0 ≤ b * u := le_of_lt (mul_pos hb hu)
  have hcu2 : 0 ≤ c * u^2 := mul_nonneg hc (sq_nonneg u)
  have hD : 0 < 1 + b * u + c * u^2 := by linarith
  have hstep : 0 < cubicRGStep b c u := by
    exact mul_pos hu hD
  unfold cubicCorrectedCoordinate cubicRGStep
  rw [Real.log_mul (ne_of_gt hu) (ne_of_gt hD)]
  field_simp [ne_of_gt hb, ne_of_gt hu, ne_of_gt hD]
  ring

/-- On a fixed weak-coupling interval, the exact cubic corrected residual is
uniformly `O(u^2)`. The explicit constant is deliberately coarse. -/
theorem cubic_corrected_residual_le_quadratic
    (b c u U : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U) :
    |cubicCorrectedCoordinate b c (cubicRGStep b c u)
        - cubicCorrectedCoordinate b c u + 1|
      ≤ (|c / b^2 - 1| * (b + c * U)^2 + c^2 / b^2) * u^2 := by
  let D : ℝ := 1 + b * u + c * u^2
  let x : ℝ := b * u + c * u^2
  have hU : 0 < U := lt_of_lt_of_le hu huU
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hD_eq : D = 1 + x := by
    dsimp [D, x]
    ring
  have hx_factor : x = u * (b + c * u) := by
    dsimp [x]
    ring
  have hfac_nonneg : 0 ≤ b + c * u := by
    have hb0 : 0 ≤ b := le_of_lt hb
    have hcu : 0 ≤ c * u := mul_nonneg hc (le_of_lt hu)
    linarith
  have hcap_nonneg : 0 ≤ b + c * U := by
    have hb0 : 0 ≤ b := le_of_lt hb
    have hcU : 0 ≤ c * U := mul_nonneg hc (le_of_lt hU)
    linarith
  have hfac_le : b + c * u ≤ b + c * U := by
    nlinarith
  have hsqfac : (b + c * u)^2 ≤ (b + c * U)^2 := by
    simpa [pow_two] using mul_self_le_mul_self hfac_nonneg hfac_le
  have hxsq : x^2 ≤ (b + c * U)^2 * u^2 := by
    rw [hx_factor]
    simp only [mul_pow]
    nlinarith [sq_nonneg u]
  have hg : |Real.log D - (D - 1) / D| ≤
      (b + c * U)^2 * u^2 := by
    rw [hD_eq]
    have hbase := abs_log_one_add_sub_frac_le_sq x hx
    have hsub : (1 + x - 1) / (1 + x) = x / (1 + x) := by ring
    rw [hsub]
    exact le_trans hbase hxsq
  have hsecond_nonneg : 0 ≤ (c^2 / b^2) * (u^2 / D) := by
    positivity
  have hsecond : (c^2 / b^2) * (u^2 / D) ≤
      (c^2 / b^2) * u^2 := by
    have hD_ge_one : 1 ≤ D := by
      rw [hD_eq]
      linarith
    have hdiv : u^2 / D ≤ u^2 := by
      rw [div_le_iff₀ hD]
      nlinarith [sq_nonneg u]
    exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  have hid := cubic_corrected_residual_identity b c u hb hc hu
  dsimp only at hid
  rw [hid]
  calc
    |(c / b^2 - 1) *
          (Real.log (1 + b * u + c * u^2) -
            ((1 + b * u + c * u^2) - 1) /
              (1 + b * u + c * u^2))
        + (c^2 / b^2) * (u^2 / (1 + b * u + c * u^2))|
      ≤ |(c / b^2 - 1) *
          (Real.log (1 + b * u + c * u^2) -
            ((1 + b * u + c * u^2) - 1) /
              (1 + b * u + c * u^2))|
        + |(c^2 / b^2) * (u^2 / (1 + b * u + c * u^2))| :=
          abs_add_le _ _
    _ ≤ |c / b^2 - 1| *
          |Real.log (1 + b * u + c * u^2) -
            ((1 + b * u + c * u^2) - 1) /
              (1 + b * u + c * u^2)|
        + (c^2 / b^2) * (u^2 / (1 + b * u + c * u^2)) := by
          exact add_le_add
            (le_of_eq (abs_mul _ _))
            (le_of_eq (by simpa [D] using abs_of_nonneg hsecond_nonneg))
    _ ≤ |c / b^2 - 1| * ((b + c * U)^2 * u^2)
        + (c^2 / b^2) * u^2 := by
          have hg' :
              |Real.log (1 + b * u + c * u^2) -
                ((1 + b * u + c * u^2) - 1) /
                  (1 + b * u + c * u^2)|
                ≤ (b + c * U)^2 * u^2 := by
            simpa [D] using hg
          exact add_le_add
            (mul_le_mul_of_nonneg_left hg' (abs_nonneg _))
            (by simpa [D] using hsecond)
    _ = (|c / b^2 - 1| * (b + c * U)^2 + c^2 / b^2) * u^2 := by
          ring

#print axioms log_one_add_sub_frac_nonneg
#print axioms log_one_add_sub_frac_le_sq
#print axioms abs_log_one_add_sub_frac_le_sq
#print axioms cubic_corrected_residual_identity
#print axioms cubic_corrected_residual_le_quadratic

end Millennium.YangMills
