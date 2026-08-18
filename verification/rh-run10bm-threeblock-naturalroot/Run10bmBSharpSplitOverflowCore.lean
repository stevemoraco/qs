import Mathlib

namespace Millennium.RH

/-- After spending the exact natural-root constraints, the determinant crossing
reduces to this one-variable cubic boundary. -/
theorem run10bmb_boundary_polynomial_identity (alpha : ℝ) :
    (((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) -
        4 * alpha ^ 2 * (1 - 2 * alpha)) =
      (800000000 * alpha ^ 3 - 402010000 * alpha ^ 2 +
          4020000 * alpha + 40401) / 100000000 := by
  ring

/-- Exact chord decomposition used to certify positivity of the cubic on the
whole rational interval `0 <= alpha <= 83/5000`. -/
theorem run10bmb_chord_decomposition (alpha : ℝ) :
    (((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) -
        4 * alpha ^ 2 * (1 - 2 * alpha)) =
      (40401 - 2432918 * alpha) / 100000000 +
        alpha * (5000 * alpha - 83) * (80000 * alpha - 38873) /
          50000000 := by
  ring

/-- The exact natural-root constraints strengthen Run10bmA's coarse
`alpha > 0.01005` bound to `alpha > 0.0166`.

This theorem begins only after the finite-dimensional singular-value producer
has supplied the determinant inequality. It does not encode primes, Hilbert
mean values, Suzuki, zeta, or RH. -/
theorem run10bmb_crossing_forces_stronger_first_split
    (alpha beta rB : ℝ)
    (ha : 0 ≤ alpha)
    (hb : 0 ≤ beta)
    (hnatural : alpha + beta ≤ 1)
    (hrB : rB ^ 2 = beta ^ 2 - alpha ^ 2)
    (hdet :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) <
        4 * alpha ^ 2 * rB ^ 2) :
    (83 / 5000 : ℝ) < alpha := by
  have hbeta : beta ≤ 1 - alpha := by
    linarith
  have honealpha : 0 ≤ 1 - alpha := by
    linarith
  have hbeta2 : beta ^ 2 ≤ (1 - alpha) ^ 2 := by
    nlinarith
  have hrBupper : rB ^ 2 ≤ 1 - 2 * alpha := by
    rw [hrB]
    nlinarith [hbeta2]
  have hqpos : 0 ≤ (101 / 100 : ℝ) ^ 2 - 1 := by
    norm_num
  have hlower :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) ≤
        ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - beta ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hqpos
    nlinarith [hbeta2]
  have ha2 : 0 ≤ 4 * alpha ^ 2 := by
    positivity
  have hupper :
      4 * alpha ^ 2 * rB ^ 2 ≤
        4 * alpha ^ 2 * (1 - 2 * alpha) := by
    exact mul_le_mul_of_nonneg_left hrBupper ha2
  have hboundaryneg :
      ((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - alpha) ^ 2) -
        4 * alpha ^ 2 * (1 - 2 * alpha) < 0 := by
    linarith
  by_contra hnot
  have hac : alpha ≤ (83 / 5000 : ℝ) := by
    exact le_of_not_gt hnot
  have hf1 : 5000 * alpha - 83 ≤ 0 := by
    nlinarith
  have hf2 : 80000 * alpha - 38873 ≤ 0 := by
    nlinarith
  have hpairs :
      0 ≤ (5000 * alpha - 83) * (80000 * alpha - 38873) := by
    exact mul_nonneg_of_nonpos_of_nonpos hf1 hf2
  have hprod :
      0 ≤ alpha * ((5000 * alpha - 83) * (80000 * alpha - 38873)) := by
    exact mul_nonneg ha hpairs
  have hlinear : 0 < 40401 - 2432918 * alpha := by
    have hc : (0 : ℝ) < 36403 / 2500 := by
      norm_num
    nlinarith
  rw [run10bmb_chord_decomposition alpha] at hboundaryneg
  have hterm :
      0 ≤ alpha * (5000 * alpha - 83) * (80000 * alpha - 38873) /
        50000000 := by
    have hprod' :
        0 ≤ alpha * (5000 * alpha - 83) * (80000 * alpha - 38873) := by
      simpa [mul_assoc] using hprod
    exact div_nonneg hprod' (by norm_num)
  have hline :
      0 < (40401 - 2432918 * alpha) / 100000000 := by
    exact div_pos hlinear (by norm_num)
  linarith

/-- The strengthened first-split bound forces the unavoidable signed support
exponent above `1.0166`. -/
theorem run10bmb_signed_support_overflow
    (alpha : ℝ)
    (ha : (83 / 5000 : ℝ) < alpha) :
    (5083 / 5000 : ℝ) < 1 + alpha := by
  linarith

/-- Exact right-hand hostile bracket: at the natural boundary
`alpha=1/60`, `beta=59/60`, `rB^2=29/30`, the scalar determinant inequality
already crosses the `101/100` cap. -/
theorem run10bmb_one_sixtieth_scalar_crossing :
    ((101 / 100 : ℝ) ^ 2 - 1) *
        ((101 / 100 : ℝ) ^ 2 - (59 / 60 : ℝ) ^ 2) <
      4 * (1 / 60 : ℝ) ^ 2 * (29 / 30 : ℝ) := by
  norm_num

/-- Exact values bracketing the true cubic threshold. -/
theorem run10bmb_boundary_at_83_over_5000 :
    (((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - (83 / 5000 : ℝ)) ^ 2) -
        4 * (83 / 5000 : ℝ) ^ 2 * (1 - 2 * (83 / 5000 : ℝ))) =
      36403 / 250000000000 := by
  norm_num

theorem run10bmb_boundary_at_one_sixtieth :
    (((101 / 100 : ℝ) ^ 2 - 1) *
          ((101 / 100 : ℝ) ^ 2 - (1 - (1 / 60 : ℝ)) ^ 2) -
        4 * (1 / 60 : ℝ) ^ 2 * (1 - 2 * (1 / 60 : ℝ))) =
      -(953 / 168750000 : ℝ) := by
  norm_num

#check run10bmb_boundary_polynomial_identity
#print axioms run10bmb_boundary_polynomial_identity
#check run10bmb_chord_decomposition
#print axioms run10bmb_chord_decomposition
#check run10bmb_crossing_forces_stronger_first_split
#print axioms run10bmb_crossing_forces_stronger_first_split
#check run10bmb_signed_support_overflow
#print axioms run10bmb_signed_support_overflow
#check run10bmb_one_sixtieth_scalar_crossing
#print axioms run10bmb_one_sixtieth_scalar_crossing
#check run10bmb_boundary_at_83_over_5000
#print axioms run10bmb_boundary_at_83_over_5000
#check run10bmb_boundary_at_one_sixtieth
#print axioms run10bmb_boundary_at_one_sixtieth

end Millennium.RH
