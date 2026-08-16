import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 permanent-tree to diameter support weakening

A permanent tree/support cost dominates the diameter of a connected reported
support. Consequently a species controlled in an `exp(κ * tree)` rooted norm
is automatically controlled in any weaker `exp(m * diameter)` norm with
`m ≤ κ`.

This is the direction needed when the joint compact/weak BKAR logarithm is
placed in a common weakened physical-diameter support norm. It is deliberately
the opposite direction from `KirkV4CompactNormEmbeddingFirewall.lean`.
-/

/-- Pointwise exponential-weight weakening from a stronger tree/support gauge
to a weaker diameter gauge. -/
theorem tree_weight_controls_diameter_weight
    (κ m tree diam : ℝ)
    (hκ : 0 ≤ κ)
    (hmκ : m ≤ κ)
    (hdiam : 0 ≤ diam)
    (hgeom : diam ≤ tree) :
    Real.exp (m * diam) ≤ Real.exp (κ * tree) := by
  have h1 : m * diam ≤ κ * diam :=
    mul_le_mul_of_nonneg_right hmκ hdiam
  have h2 : κ * diam ≤ κ * tree :=
    mul_le_mul_of_nonneg_left hgeom hκ
  exact Real.exp_le_exp.mpr (h1.trans h2)

/-- Finite row version: nonnegative coefficients preserve the weakening
pointwise under summation. -/
theorem tree_row_controls_diameter_row
    {ι : Type*}
    (s : Finset ι)
    (κ m : ℝ)
    (tree diam coeff : ι → ℝ)
    (hκ : 0 ≤ κ)
    (hmκ : m ≤ κ)
    (hdiam : ∀ i ∈ s, 0 ≤ diam i)
    (hgeom : ∀ i ∈ s, diam i ≤ tree i)
    (hcoeff : ∀ i ∈ s, 0 ≤ coeff i) :
    ∑ i ∈ s, Real.exp (m * diam i) * coeff i ≤
      ∑ i ∈ s, Real.exp (κ * tree i) * coeff i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (tree_weight_controls_diameter_weight κ m (tree i) (diam i)
      hκ hmκ (hdiam i hi) (hgeom i hi))
    (hcoeff i hi)

#print axioms tree_weight_controls_diameter_weight
#print axioms tree_row_controls_diameter_row

end Millennium.YangMills
