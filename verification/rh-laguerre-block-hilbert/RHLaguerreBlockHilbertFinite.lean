import Mathlib

/-!
# RH weighted Laguerre block-Hilbert finite core

HONESTY BOUNDARY

This file verifies only scalar bookkeeping in a phase-preserving exact-confluent
Hardy interpolation theorem. It does not formalize Laguerre polynomials, the
Montgomery--Vaughan inequality, Hardy spaces, divided differences, zeta zeros,
or RH.
-/

namespace MillenniumBraid
namespace RHLaguerreBlockHilbertFinite

theorem defect_bookkeeping (pi r K : ℝ) :
    2 * pi * r * K + 4 * pi * r * K + 2 * pi * r =
      2 * pi * r * (3 * K + 1) := by
  ring

theorem lower_from_absolute_defect
    (D C delta : ℝ)
    (habs : |C| ≤ delta * D) :
    (1 - delta) * D ≤ D + C := by
  have hpair : -delta * D ≤ C ∧ C ≤ delta * D := abs_le.mp habs
  linarith

theorem upper_from_absolute_defect
    (D C delta : ℝ)
    (habs : |C| ≤ delta * D) :
    D + C ≤ (1 + delta) * D := by
  have hpair : -delta * D ≤ C ∧ C ≤ delta * D := abs_le.mp habs
  linarith

theorem low_density_floor_positive
    (pi r K : ℝ)
    (h : 2 * pi * r * (3 * K + 1) < 1) :
    0 < 1 - 2 * pi * r * (3 * K + 1) := by
  linarith

theorem defect_le_eight
    (pi r K : ℝ)
    (hpr : 0 ≤ pi * r)
    (hK : 1 ≤ K) :
    2 * pi * r * (3 * K + 1) ≤ 8 * pi * r * K := by
  have hcore : 2 * (3 * K + 1) ≤ 8 * K := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hcore hpr
  calc
    2 * pi * r * (3 * K + 1)
        = (pi * r) * (2 * (3 * K + 1)) := by ring
    _ ≤ (pi * r) * (8 * K) := hmul
    _ = 8 * pi * r * K := by ring

theorem simple_floor_positive
    (pi r K : ℝ)
    (hpr : 0 ≤ pi * r)
    (hK : 1 ≤ K)
    (hsmall : 8 * pi * r * K < 1) :
    0 < 1 - 2 * pi * r * (3 * K + 1) := by
  have hdef := defect_le_eight pi r K hpr hK
  linarith

theorem exact_low_density_lower_bound
    (D C pi r K : ℝ)
    (habs : |C| ≤ (2 * pi * r * (3 * K + 1)) * D) :
    (1 - 2 * pi * r * (3 * K + 1)) * D ≤ D + C := by
  exact lower_from_absolute_defect D C
    (2 * pi * r * (3 * K + 1)) habs

theorem exact_low_density_upper_bound
    (D C pi r K : ℝ)
    (habs : |C| ≤ (2 * pi * r * (3 * K + 1)) * D) :
    D + C ≤ (1 + 2 * pi * r * (3 * K + 1)) * D := by
  exact upper_from_absolute_defect D C
    (2 * pi * r * (3 * K + 1)) habs

inductive ClusterInput where
  | exactConfluent
  | perturbedExponentials
  deriving DecidableEq

theorem exact_ne_perturbed :
    ClusterInput.exactConfluent ≠ ClusterInput.perturbedExponentials := by
  decide

#print axioms defect_bookkeeping
#print axioms lower_from_absolute_defect
#print axioms upper_from_absolute_defect
#print axioms low_density_floor_positive
#print axioms defect_le_eight
#print axioms simple_floor_positive
#print axioms exact_low_density_lower_bound
#print axioms exact_low_density_upper_bound
#print axioms exact_ne_perturbed

end RHLaguerreBlockHilbertFinite
end MillenniumBraid
