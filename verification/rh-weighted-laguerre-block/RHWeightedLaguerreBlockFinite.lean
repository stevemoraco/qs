import Mathlib

/-!
# RH weighted Laguerre block finite firewalls

HONESTY BOUNDARY

This file verifies only finite scalar and logical interfaces used in the
common-damping exact-confluent block theorem:

* boundary and two centered-derivative error budgets combine exactly;
* an absolute cross-term defect gives two-sided quadratic-form bounds;
* a strict defect below one gives a positive lower floor;
* a local block floor composes with a global subspace floor;
* exact confluent data and perturbed-cluster data are distinct types.

It does not formalize Montgomery--Vaughan's Hilbert inequality, Laguerre
orthogonality, the exact triangular singular-value formula, integration by
parts, Hardy spaces, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHWeightedLaguerreBlockFinite

/-- The boundary contribution `2πrK` and two centered-derivative
contributions `πrq` combine to `2πr(K+q)`. -/
theorem defect_bookkeeping (pi r K q : ℝ) :
    2 * pi * r * K + pi * r * q + pi * r * q =
      2 * pi * r * (K + q) := by
  ring

/-- Three signed contributions, each enclosed by a nonnegative scalar budget,
combine without a hidden cancellation assumption. -/
theorem combine_three_signed_budgets
    (boundary left right D b q : ℝ)
    (hD : 0 ≤ D)
    (hb : 0 ≤ b)
    (hq : 0 ≤ q)
    (hboundaryLower : -(b * D) ≤ boundary)
    (hboundaryUpper : boundary ≤ b * D)
    (hleftLower : -(q * D) ≤ left)
    (hleftUpper : left ≤ q * D)
    (hrightLower : -(q * D) ≤ right)
    (hrightUpper : right ≤ q * D) :
    -((b + 2 * q) * D) ≤ boundary + left + right ∧
      boundary + left + right ≤ (b + 2 * q) * D := by
  constructor <;> nlinarith

/-- An absolute cross-term bound gives the lower quadratic-form estimate. -/
theorem lower_from_absolute_defect
    (D C delta : ℝ)
    (habs : |C| ≤ delta * D) :
    D + C ≥ (1 - delta) * D := by
  have hneg : -(delta * D) ≤ C := neg_le_of_abs_le habs
  nlinarith

/-- The same absolute cross-term bound gives the upper estimate. -/
theorem upper_from_absolute_defect
    (D C delta : ℝ)
    (habs : |C| ≤ delta * D) :
    D + C ≤ (1 + delta) * D := by
  have hpos : C ≤ delta * D := le_of_abs_le habs
  nlinarith

/-- A strict relative defect below one leaves a strictly positive scalar floor. -/
theorem strict_defect_positive_floor
    (delta : ℝ)
    (hdelta : delta < 1) :
    0 < 1 - delta := by
  linarith

/-- The exact displayed low-density condition is merely the assertion that the
relative defect is below one. -/
theorem low_density_condition
    (pi r K q : ℝ)
    (hsmall : 2 * pi * r * (K + q) < 1) :
    0 < 1 - 2 * pi * r * (K + q) := by
  linarith

/-- A positive global subspace floor composes with a positive local-coordinate
floor. This is the finite scalar core of passing from separate block energies
to raw coefficient energy. -/
theorem compose_global_and_local_floors
    (Q D coeff A gamma : ℝ)
    (hA : 0 ≤ A)
    (hgamma : 0 ≤ gamma)
    (hglobal : A * D ≤ Q)
    (hlocal : gamma * coeff ≤ D) :
    (A * gamma) * coeff ≤ Q := by
  calc
    (A * gamma) * coeff = A * (gamma * coeff) := by ring
    _ ≤ A * D := mul_le_mul_of_nonneg_left hlocal hA
    _ ≤ Q := hglobal

/-- A type firewall: exact polynomial-confluent blocks and clusters of distinct
perturbed exponentials are not definitionally interchangeable. -/
inductive ClusterInput where
  | exactConfluent
  | perturbedExponentials
  deriving DecidableEq

theorem exactConfluent_ne_perturbed :
    ClusterInput.exactConfluent ≠ ClusterInput.perturbedExponentials := by
  decide

/-- A theorem whose premise is exact-confluent remains confined to that input
until a separate transfer map is supplied. -/
theorem exact_only_stays_exact
    (P : ClusterInput → Prop)
    (h : P ClusterInput.exactConfluent) :
    P ClusterInput.exactConfluent := h

#print axioms defect_bookkeeping
#print axioms combine_three_signed_budgets
#print axioms lower_from_absolute_defect
#print axioms upper_from_absolute_defect
#print axioms strict_defect_positive_floor
#print axioms low_density_condition
#print axioms compose_global_and_local_floors
#print axioms exactConfluent_ne_perturbed
#print axioms exact_only_stays_exact

end RHWeightedLaguerreBlockFinite
end MillenniumBraid
