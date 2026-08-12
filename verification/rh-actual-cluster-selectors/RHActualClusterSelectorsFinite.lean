import Mathlib

/-!
# RH actual-cluster selector finite scalar firewall

HONESTY BOUNDARY

This file verifies only scalar and logical consequences used by an explicit
actual-cluster Hardy-space selector theorem. It does not formalize
pseudohyperbolic disks, Blaschke products, confluent interpolation, Hardy model
spaces, multiplier adjoints, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHActualClusterSelectorsFinite

theorem external_eta_pos
    (A h : ℝ)
    (hA : 0 < A)
    (hh : 0 < h) :
    0 < (2 * Real.pi * A / h) /
      Real.sinh (2 * Real.pi * A / h) := by
  have harg : 0 < 2 * Real.pi * A / h := by positivity
  have hsinh : 0 < Real.sinh (2 * Real.pi * A / h) :=
    Real.sinh_pos_iff.mpr harg
  positivity

theorem lower_riesz_from_sign_average
    (sumSq totalSq C : ℝ)
    (hC : 0 < C)
    (hbound : sumSq ≤ C ^ 2 * totalSq) :
    C⁻¹ ^ 2 * sumSq ≤ totalSq := by
  have hC2 : 0 < C ^ 2 := sq_pos_of_pos hC
  have hdiv : sumSq / (C ^ 2) ≤ totalSq := (div_le_iff₀ hC2).2 hbound
  calc
    C⁻¹ ^ 2 * sumSq = sumSq / (C ^ 2) := by
      field_simp [ne_of_gt hC]
      ring
    _ ≤ totalSq := hdiv

theorem actual_cluster_floor_positive
    (S P : ℝ)
    (hS : 0 < S)
    (hP : 0 < P) :
    0 < (S * P)⁻¹ ^ 2 := by
  positivity

/-- The two-sided Riesz conclusion has distinct lower and upper scalar forms. -/
theorem two_sided_riesz_scalar
    (sumSq totalSq C : ℝ)
    (hC : 0 < C)
    (hlower : sumSq ≤ C ^ 2 * totalSq)
    (hupper : totalSq ≤ C ^ 2 * sumSq) :
    C⁻¹ ^ 2 * sumSq ≤ totalSq ∧
      totalSq ≤ C ^ 2 * sumSq := by
  constructor
  · exact lower_riesz_from_sign_average sumSq totalSq C hC hlower
  · exact hupper

inductive ClusterGeometry where
  | sameVerticalLineSeparatedContours
  | unrestrictedZetaClusters
  deriving DecidableEq

theorem same_line_ne_unrestricted :
    ClusterGeometry.sameVerticalLineSeparatedContours ≠
      ClusterGeometry.unrestrictedZetaClusters := by
  decide

#print axioms external_eta_pos
#print axioms lower_riesz_from_sign_average
#print axioms actual_cluster_floor_positive
#print axioms two_sided_riesz_scalar
#print axioms same_line_ne_unrestricted

end RHActualClusterSelectorsFinite
end MillenniumBraid
