import Mathlib

namespace B4NSStaticTransportObstruction

/-- Rational polynomial core of the explicit static low/high transport output.
    With `u = sqrt 2`, `M = sqrt (2n^2+2n+1)`, the right side is the
    numerator of four times the positive-helicity output coefficient. -/
theorem staticTransportNumeratorLower
    {n M u : ℝ}
    (hn : 3 ≤ n)
    (hM : 0 ≤ M)
    (hu : 4 / 3 ≤ u) :
    n * M ≤ 2 * n^2 + u * n * M - M - 1 := by
  have hthird : (1 / 3 : ℝ) ≤ u - 1 := by linarith
  have hu1 : 0 ≤ u - 1 := by linarith
  have hprod : (1 / 3 : ℝ) * 3 ≤ (u - 1) * n := by
    exact mul_le_mul hthird hn (by norm_num) hu1
  have hshift : n ≤ u * n - 1 := by
    nlinarith
  have hmul : n * M ≤ (u * n - 1) * M :=
    mul_le_mul_of_nonneg_right hshift hM
  have hquad : 0 ≤ 2 * n^2 - 1 := by
    nlinarith [sq_nonneg n]
  nlinarith

/-- Cross-multiplied coefficient consequence.  If an explicit static output
    has numerator `2n^2 + u n M - M - 1`, then its coefficient is at least
    `K n / 4`; hence it grows on the child scale rather than the parent scale. -/
theorem staticTransportCoefficientCrossMultiplied
    {n M u K numerator coefficient : ℝ}
    (hn : 3 ≤ n)
    (hM : 0 ≤ M)
    (hu : 4 / 3 ≤ u)
    (hK : 0 ≤ K)
    (hNumerator : numerator = 2 * n^2 + u * n * M - M - 1)
    (hCoefficient : 4 * M * coefficient = K * numerator) :
    K * n * M ≤ 4 * M * coefficient := by
  have hbase := staticTransportNumeratorLower hn hM hu
  calc
    K * n * M = K * (n * M) := by ring
    _ ≤ K * (2 * n^2 + u * n * M - M - 1) :=
      mul_le_mul_of_nonneg_left hbase hK
    _ = K * numerator := by rw [hNumerator]
    _ = 4 * M * coefficient := hCoefficient.symm

/-- A child-scale transport term cannot be silently reclassified as a
    parent-scale error when the scale ratio is unbounded. -/
theorem childScaleExceedsAnyFixedParentMultiple
    {C n : ℝ}
    (hLarge : 4 * C < n) :
    C < n / 4 := by
  linarith

/-- A time-dependent interaction representation may cancel a skew transport
    coefficient without changing the quadratic energy. -/
theorem phaseRotationPreservesQuadraticEnergy
    (omega X Y : ℝ) :
    X * (-omega * Y) + Y * (omega * X) = 0 := by
  ring

#print axioms staticTransportNumeratorLower
#print axioms staticTransportCoefficientCrossMultiplied
#print axioms childScaleExceedsAnyFixedParentMultiple
#print axioms phaseRotationPreservesQuadraticEnergy

end B4NSStaticTransportObstruction
