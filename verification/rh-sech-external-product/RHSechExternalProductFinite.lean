import Mathlib

/-!
# RH sech external-product finite firewalls

HONESTY BOUNDARY

This file verifies only finite scalar and logical interfaces used by the
half-integer external-Blaschke-product sharpening:

* the exact center-index geometry leaves `(m - 1/2)h`, not merely `mh/2`;
* the half-integer square is the odd-lattice square after rescaling;
* for a base in `[0,1]`, having at most `2K` factors gives the exponent in the
  direction required by the lower product bound;
* replacing an external-product floor by a larger positive floor reduces the
  corresponding reciprocal requirement;
* abstract cluster-selector geometry is not a zeta-cluster decomposition.

It does not formalize the canonical infinite product for `cosh`, Blaschke
products, confluent divided differences, Hardy/model spaces, multiplier
adjoints, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHSechExternalProductFinite

/-- The exact contour budget leaves a half-integer center distance. -/
theorem half_integer_distance
    (m h contourRadius clusterRadius : ℝ)
    (hm : 1 ≤ m)
    (hh : 0 ≤ h)
    (hbudget : contourRadius + clusterRadius ≤ h / 2) :
    (m - 1 / 2) * h ≤
      m * h - contourRadius - clusterRadius := by
  nlinarith

/-- The half-integer lattice is exactly the odd lattice after doubling. -/
theorem half_integer_odd_index (m : ℝ) :
    2 * (m - 1 / 2) = 2 * m - 1 := by
  ring

/-- Squared form used in the Cauchy-factor denominator. -/
theorem half_integer_odd_square (m : ℝ) :
    4 * (m - 1 / 2) ^ 2 = (2 * m - 1) ^ 2 := by
  ring

/-- Powers of a number in `[0,1]` decrease with the natural exponent. -/
theorem pow_antitone_on_unit_interval
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (n m : ℕ)
    (hnm : n ≤ m) :
    q ^ m ≤ q ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add]
  have hk : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1
  have hn : 0 ≤ q ^ n := pow_nonneg hq0 n
  calc
    q ^ n * q ^ k ≤ q ^ n * 1 :=
      mul_le_mul_of_nonneg_left hk hn
    _ = q ^ n := by ring

/-- If there are at most `2K` factors, the lower exponent can safely be
replaced by `2K`; this records the direction that is easy to reverse by
mistake. -/
theorem at_most_twoK_exponent_direction
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (factorCount K : ℕ)
    (hcount : factorCount ≤ 2 * K) :
    q ^ (2 * K) ≤ q ^ factorCount := by
  exact pow_antitone_on_unit_interval q hq0 hq1 factorCount (2 * K) hcount

/-- A larger positive external-product floor makes a nonnegative reciprocal
requirement smaller. This is the scalar core of replacing the old sinh floor
by the new sech floor. -/
theorem larger_floor_reduces_reciprocal_requirement
    (oldFloor newFloor localConstant : ℝ)
    (hold : 0 < oldFloor)
    (hnew : 0 < newFloor)
    (hlocal : 0 ≤ localConstant)
    (hfloor : oldFloor ≤ newFloor) :
    localConstant / newFloor ≤ localConstant / oldFloor := by
  apply (div_le_div_iff₀ hnew hold).2
  exact mul_le_mul_of_nonneg_left hfloor hlocal

/-- A smaller positive selector constant has a smaller square. -/
theorem smaller_constant_stronger_cross_floor
    (sharp coarse : ℝ)
    (hsharp : 0 < sharp)
    (horder : sharp ≤ coarse) :
    sharp ^ 2 ≤ coarse ^ 2 := by
  have hcoarse : 0 ≤ coarse := le_trans (le_of_lt hsharp) horder
  nlinarith

/-- Type firewall: the abstract selector hypotheses are not definitionally the
zeta-specific packet theorem still required downstream. -/
inductive ClusterInput where
  | abstractSelectorGeometry
  | zetaSpecificPacket
  deriving DecidableEq

theorem abstract_geometry_ne_zeta_packet :
    ClusterInput.abstractSelectorGeometry ≠
      ClusterInput.zetaSpecificPacket := by
  decide

/-- A result proved for abstract cluster geometry remains confined there until
a separate zeta-specific decomposition is supplied. -/
theorem abstract_result_stays_abstract
    (P : ClusterInput → Prop)
    (h : P ClusterInput.abstractSelectorGeometry) :
    P ClusterInput.abstractSelectorGeometry := h

#print axioms half_integer_distance
#print axioms half_integer_odd_index
#print axioms half_integer_odd_square
#print axioms pow_antitone_on_unit_interval
#print axioms at_most_twoK_exponent_direction
#print axioms larger_floor_reduces_reciprocal_requirement
#print axioms smaller_constant_stronger_cross_floor
#print axioms abstract_geometry_ne_zeta_packet
#print axioms abstract_result_stays_abstract

end RHSechExternalProductFinite
end MillenniumBraid
