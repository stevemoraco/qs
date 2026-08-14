import Millennium.YangMills.RGQuarticPerturbation
import Millennium.YangMills.RGAccumulatedRemainder

/-!
# Perturbed two-loop RG crossing remainder

This file composes three previously isolated finite ingredients:

1. the exact-cubic two-loop corrected-coordinate residual is `O(u^2)`;
2. an `O(u^4)` perturbation changes that corrected coordinate by only `O(u^2)`;
3. quadratic RG growth makes a local `O(u^2)` defect globally summable up to a
   fixed weak-coupling threshold.

For a trajectory satisfying

    u_{n+1} = u_n * (1 + b*u_n + c*u_n^2) + r_n,
    |r_n| <= R*u_n^4,

with all `u_n` in a fixed interval `(0,U]`, the corrected crossing-time
coordinate has a regulator-independent `O(1)` remainder, provided the quartic
error is small enough to preserve positivity and quadratic growth.

Honesty boundary: this is still a finite scalar recurrence theorem. It does not
prove that any nonperturbative Yang--Mills blocking map has such a recurrence
uniformly in cutoff, volume, or boundary condition; it does not identify `b,c`
with a specified Yang--Mills scheme; and it does not prove a physical spectral
gap or Osterwalder--Schrader continuum construction.
-/

namespace Millennium.YangMills

/-- The explicit exact-cubic local-residual constant. -/
noncomputable def cubicLocalResidualConstant (b c U : ℝ) : ℝ :=
  |c / b^2 - 1| * (b + c * U)^2 + c^2 / b^2

/-- The explicit extra local-residual cost of an `O(u^4)` perturbation. -/
noncomputable def quarticPerturbationResidualConstant
    (b c U R : ℝ) : ℝ :=
  2 * R * (1 / b + |c / b^2 - 1| * U)

/-- Total local-residual constant for the cubic-plus-quartic recurrence. -/
noncomputable def perturbedLocalResidualConstant
    (b c U R : ℝ) : ℝ :=
  cubicLocalResidualConstant b c U +
    quarticPerturbationResidualConstant b c U R

/-- The total residual constant is nonnegative on the weak-coupling domain. -/
theorem perturbedLocalResidualConstant_nonneg
    (b c U R : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hU : 0 ≤ U) (hR : 0 ≤ R) :
    0 ≤ perturbedLocalResidualConstant b c U R := by
  unfold perturbedLocalResidualConstant cubicLocalResidualConstant
    quarticPerturbationResidualConstant
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hinvb : 0 < 1 / b := one_div_pos.mpr hb
  positivity

/-- One-step composition theorem: the exact cubic residual plus an `O(u^4)`
perturbation still leaves only an `O(u^2)` corrected-coordinate defect. -/
theorem perturbed_cubic_corrected_residual_le_quadratic
    (b c u U R r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U)
    (hR : 0 ≤ R) (hr : |r| ≤ R * u^4)
    (hsmall : R * U^3 ≤ 1 / 2) :
    |cubicCorrectedCoordinate b c (cubicRGStep b c u + r) -
        cubicCorrectedCoordinate b c u + 1|
      ≤ perturbedLocalResidualConstant b c U R * u^2 := by
  have hcubic := cubic_corrected_residual_le_quadratic
    b c u U hb hc hu huU
  have hpert := cubic_corrected_coordinate_quartic_perturbation_le_quadratic
    b c u U R r hb hc hu huU hR hr hsmall
  have hsplit :
      cubicCorrectedCoordinate b c (cubicRGStep b c u + r) -
          cubicCorrectedCoordinate b c u + 1
        = (cubicCorrectedCoordinate b c (cubicRGStep b c u + r) -
            cubicCorrectedCoordinate b c (cubicRGStep b c u))
          + (cubicCorrectedCoordinate b c (cubicRGStep b c u) -
            cubicCorrectedCoordinate b c u + 1) := by ring
  rw [hsplit]
  calc
    |(cubicCorrectedCoordinate b c (cubicRGStep b c u + r) -
          cubicCorrectedCoordinate b c (cubicRGStep b c u))
        + (cubicCorrectedCoordinate b c (cubicRGStep b c u) -
          cubicCorrectedCoordinate b c u + 1)|
      ≤ |cubicCorrectedCoordinate b c (cubicRGStep b c u + r) -
          cubicCorrectedCoordinate b c (cubicRGStep b c u)|
        + |cubicCorrectedCoordinate b c (cubicRGStep b c u) -
          cubicCorrectedCoordinate b c u + 1| := abs_add_le _ _
    _ ≤ quarticPerturbationResidualConstant b c U R * u^2
        + cubicLocalResidualConstant b c U * u^2 := by
          unfold quarticPerturbationResidualConstant cubicLocalResidualConstant
          exact add_le_add hpert hcubic
    _ = perturbedLocalResidualConstant b c U R * u^2 := by
          unfold perturbedLocalResidualConstant
          ring

/-- Main finite shooting theorem. For a cubic-plus-`O(u^4)` trajectory that
stays in `(0,U]`, the two-loop corrected crossing-time remainder is uniformly
bounded independently of the number of RG steps. -/
theorem perturbed_cubic_crossing_remainder_uniform
    (u r : ℕ → ℝ) (N : ℕ)
    (b c U R : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hsmallPos : R * U^3 ≤ 1 / 2)
    (hsmallGrowth : R * U^2 ≤ b / 2)
    (hpos : ∀ n ≤ N, 0 < u n)
    (hupper : ∀ n ≤ N, u n ≤ U)
    (hrec : ∀ n < N,
      u (n + 1) = cubicRGStep b c (u n) + r n)
    (hquartic : ∀ n < N,
      |r n| ≤ R * (u n)^4) :
    |cubicCorrectedCoordinate b c (u N) -
        cubicCorrectedCoordinate b c (u 0) + (N : ℝ)|
      ≤ (perturbedLocalResidualConstant b c U R / (b / 2)) * U := by
  let phi : ℕ → ℝ := fun n => cubicCorrectedCoordinate b c (u n)
  have hbeta : 0 < b / 2 := half_pos hb
  have hu0 : 0 ≤ u 0 := le_of_lt (hpos 0 (Nat.zero_le N))
  have hUN : u N ≤ U := hupper N (le_refl N)
  have hU0 : 0 ≤ U := le_trans hu0 (hupper 0 (Nat.zero_le N))
  have hK : 0 ≤ perturbedLocalResidualConstant b c U R :=
    perturbedLocalResidualConstant_nonneg b c U R hb hc hU0 hR
  have hgrowth : ∀ n < N,
      (b / 2) * (u n)^2 ≤ u (n + 1) - u n := by
    intro n hn
    rw [hrec n hn]
    exact quartic_perturbation_preserves_quadratic_growth
      b c (u n) U R (r n) hb hc
      (hpos n (Nat.le_of_lt hn))
      (hupper n (Nat.le_of_lt hn))
      hR (hquartic n hn) hsmallGrowth
  have hlocal : ∀ n < N,
      |correctedResidual phi n| ≤
        perturbedLocalResidualConstant b c U R * (u n)^2 := by
    intro n hn
    unfold correctedResidual phi
    rw [hrec n hn]
    exact perturbed_cubic_corrected_residual_le_quadratic
      b c (u n) U R (r n) hb hc
      (hpos n (Nat.le_of_lt hn))
      (hupper n (Nat.le_of_lt hn))
      hR (hquartic n hn) hsmallPos
  simpa [phi] using
    corrected_remainder_uniform_at_fixed_threshold
      u phi N hbeta hK hu0 hUN hgrowth hlocal

#print axioms perturbedLocalResidualConstant_nonneg
#print axioms perturbed_cubic_corrected_residual_le_quadratic
#print axioms perturbed_cubic_crossing_remainder_uniform

end Millennium.YangMills
