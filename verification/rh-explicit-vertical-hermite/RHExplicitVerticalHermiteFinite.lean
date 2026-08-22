import Mathlib

/-!
# Explicit vertical Hermite-selector finite scalar firewall

HONESTY BOUNDARY

This file verifies only scalar consequences and model-type distinctions used by
an explicit Hardy-space selector theorem. It does not formalize Blaschke
products, Hardy spaces, multiplier adjoints, Rademacher averaging in Hilbert
space, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHExplicitVerticalHermiteFinite

theorem vertical_delta_pos
    (r : ℝ) (hr : 0 < r) :
    0 < 2 * Real.pi * r / Real.sinh (2 * Real.pi * r) := by
  have harg : 0 < 2 * Real.pi * r := by positivity
  have hsinh : 0 < Real.sinh (2 * Real.pi * r) := Real.sinh_pos_iff.mpr harg
  positivity

theorem vertical_M_pos
    (r delta : ℝ)
    (hr : 0 < r)
    (hdelta : 0 < delta) :
    0 < delta⁻¹ * (8 + (4 * Real.pi ^ 2 / 3) * r ^ 2) := by
  have hbracket : 0 < 8 + (4 * Real.pi ^ 2 / 3) * r ^ 2 := by positivity
  positivity

theorem selector_exponents_reparam (n : ℕ) :
    (3 * (n + 1) - 2 = 3 * n + 1) ∧
    (2 * (n + 1) - 1 = 2 * n + 1) ∧
    (6 * (n + 1) - 4 = 6 * n + 2) ∧
    (4 * (n + 1) - 2 = 4 * n + 2) := by
  omega

theorem selector_square_reparam
    (M : ℝ) (n : ℕ) :
    ((2 : ℝ) ^ (3 * n + 1) * M ^ (2 * n + 1)) ^ 2 =
      (2 : ℝ) ^ (6 * n + 2) * M ^ (4 * n + 2) := by
  rw [mul_pow]
  rw [← pow_mul]
  rw [← pow_mul]
  congr 1 <;> omega

theorem selector_inverse_square_reparam
    (M : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ (3 * n + 1) * M ^ (2 * n + 1))⁻¹) ^ 2 =
      ((2 : ℝ) ^ (6 * n + 2) * M ^ (4 * n + 2))⁻¹ := by
  rw [inv_pow]
  rw [selector_square_reparam]

theorem riesz_lower_from_randomized_bound
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

theorem selector_budget_positive
    (M : ℝ) (n : ℕ)
    (hM : 0 < M) :
    0 < (2 : ℝ) ^ (3 * n + 1) * M ^ (2 * n + 1) := by
  positivity

inductive ClusterGeometry where
  | exactLocalModelSpaces
  | actualPerturbedClusters
  deriving DecidableEq

theorem exact_model_ne_actual_cluster :
    ClusterGeometry.exactLocalModelSpaces ≠
      ClusterGeometry.actualPerturbedClusters := by
  decide

#print axioms vertical_delta_pos
#print axioms vertical_M_pos
#print axioms selector_exponents_reparam
#print axioms selector_square_reparam
#print axioms selector_inverse_square_reparam
#print axioms riesz_lower_from_randomized_bound
#print axioms selector_budget_positive
#print axioms exact_model_ne_actual_cluster

end RHExplicitVerticalHermiteFinite
end MillenniumBraid
