import Mathlib

/-!
# Symmetric restriction-density finite core

This file formalizes the arithmetic/cardinality skeleton behind the following
paper theorem: a symmetric Boolean function that remains nonconstant after all
bit fixings of depth `r` has both color classes of size at least
`Nat.choose n (r / 2)`.

The circuit-theoretic definitions, the extraction of central accepted/rejected
weights from a resilient symmetric function, and the external gate-elimination
sources are deliberately not encoded here.  Instead, the load-bearing finite
transfer is stated with those two weights as explicit data.
-/

namespace MillenniumRun204.PNPSymmetricRestrictionDensity

/-- `t` is the integer floor of half of `r`, expressed without division. -/
def IsFloorHalf (r t : ℕ) : Prop :=
  2 * t ≤ r ∧ r ≤ 2 * t + 1

/-- A weight lies in the interval exposed by fixing `t` ones and `r-t` zeros. -/
def CentralRestrictionWeight (n r t k : ℕ) : Prop :=
  t ≤ k ∧ k + (r - t) ≤ n

/-- The actual natural-number floor satisfies the division-free specification. -/
theorem nat_floor_half_is_floor_half (r : ℕ) : IsFloorHalf r (r / 2) := by
  constructor <;> omega

/-- Every exposed weight also lies at distance at least `t` from the upper edge. -/
theorem central_restriction_add_half_le
    {n r t k : ℕ}
    (hhalf : IsFloorHalf r t)
    (hk : CentralRestrictionWeight n r t k) :
    k + t ≤ n := by
  unfold IsFloorHalf CentralRestrictionWeight at *
  omega

/-- A central-layer size function is no smaller away from either boundary. -/
def CentralLayerDominance
    (layerSize : ℕ → ℕ) (n t : ℕ) : Prop :=
  ∀ k : ℕ, t ≤ k → k + t ≤ n → layerSize t ≤ layerSize k

/-- Explicit accepted and rejected Hamming weights in one central restriction. -/
structure TwoColorCentralWitness (n r t : ℕ) where
  oneWeight : ℕ
  zeroWeight : ℕ
  oneCentral : CentralRestrictionWeight n r t oneWeight
  zeroCentral : CentralRestrictionWeight n r t zeroWeight

/--
If symmetry supplies a complete accepted layer and a complete rejected layer at
the two central weights, then both color classes dominate the boundary layer.
-/
theorem two_color_support_lower_bound
    (layerSize : ℕ → ℕ)
    {n r t oneSize zeroSize : ℕ}
    (hhalf : IsFloorHalf r t)
    (hdom : CentralLayerDominance layerSize n t)
    (w : TwoColorCentralWitness n r t)
    (hone : layerSize w.oneWeight ≤ oneSize)
    (hzero : layerSize w.zeroWeight ≤ zeroSize) :
    layerSize t ≤ oneSize ∧ layerSize t ≤ zeroSize := by
  constructor
  · exact (hdom w.oneWeight w.oneCentral.1
      (central_restriction_add_half_le hhalf w.oneCentral)).trans hone
  · exact (hdom w.zeroWeight w.zeroCentral.1
      (central_restriction_add_half_le hhalf w.zeroCentral)).trans hzero

/-- Fixing more than `w` variables to one makes total weight `w` impossible. -/
theorem too_many_fixed_ones_kill_exact_weight
    {w fixedOnes totalWeight : ℕ}
    (hfixed : w < fixedOnes)
    (htotal : fixedOnes ≤ totalWeight) :
    totalWeight ≠ w := by
  omega

/-- Fixing more than `n-w` variables to zero makes total weight `w` impossible. -/
theorem too_many_fixed_zeros_kill_exact_weight
    {n w fixedZeros totalWeight : ℕ}
    (hw : w ≤ n)
    (hfixed : n - w < fixedZeros)
    (htotal : totalWeight ≤ n - fixedZeros) :
    totalWeight ≠ w := by
  omega

/-- The two standard attacks kill a single exact layer after one extra fixing. -/
theorem exact_layer_resilience_upper_attacks
    {n w : ℕ} (hw : w ≤ n) :
    (∀ totalWeight, w + 1 ≤ totalWeight → totalWeight ≠ w) ∧
    (∀ totalWeight, totalWeight ≤ n - (n - w + 1) → totalWeight ≠ w) := by
  constructor
  · intro totalWeight htotal
    exact too_many_fixed_ones_kill_exact_weight (by omega) htotal
  · intro totalWeight htotal
    exact too_many_fixed_zeros_kill_exact_weight hw (by omega) htotal

#print axioms nat_floor_half_is_floor_half
#print axioms central_restriction_add_half_le
#print axioms two_color_support_lower_bound
#print axioms too_many_fixed_ones_kill_exact_weight
#print axioms too_many_fixed_zeros_kill_exact_weight
#print axioms exact_layer_resilience_upper_attacks

end MillenniumRun204.PNPSymmetricRestrictionDensity
