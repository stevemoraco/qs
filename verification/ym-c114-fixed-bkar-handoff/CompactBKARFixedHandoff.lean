import Mathlib

namespace Millennium.YangMills

/-!
# Fixed compact-to-BKAR handoff ledger

Finite real-algebra firewall for the current Kirk-v4 joint-admission audit.

The source-level analytic gate is deliberately not encoded here.  The intended
input is one regulator-independent norm-transfer constant `Kmap` from the
compact outer-tube coefficient row to the weakened BKAR species row.  A fixed
inner-tube distance `r > 0` then gives the standard first/second Cauchy
recertification multiplier, and one fixed maximum pays both printed half-margin
conditions used by the BKAR admission ledger.

This file proves only the scalar implication.  It does not prove the required
infinite-dimensional norm inclusion, the outer-tube compact row, Kirk's
Theorem 6.43, continuum reconstruction, a Yang--Mills mass gap, or a prize
theorem.
-/

noncomputable def compactRecertificationMultiplier (r : ℝ) : ℝ :=
  1 / (2 * r) + 1 / r ^ 2

noncomputable def compactBKARHalfMarginCost
    (Kmap r covNorm allocCost treeCost : ℝ) : ℝ :=
  max
    (8 * covNorm * allocCost * compactRecertificationMultiplier r * Kmap)
    (2 * treeCost * Kmap)

theorem compact_recertification_multiplier_pos
    (r : ℝ) (hr : 0 < r) :
    0 < compactRecertificationMultiplier r := by
  dsimp [compactRecertificationMultiplier]
  positivity

/--
If one fixed scalar `C_E` dominates both the regulator-allocation cost and the
parent-normalized tree-link cost, then `C_E * eta <= 1` places both quantities
inside the printed `1/2` BKAR margins.  The factor eight is exactly the
`4 * ||C||` Gram condition plus the desired half-margin; the factor two is the
parent-normalized tree half-margin.
-/
theorem one_fixed_cost_pays_both_bkar_half_margins
    (eta Kmap r covNorm allocCost treeCost : ℝ)
    (heta : 0 ≤ eta)
    (hbudget :
      compactBKARHalfMarginCost Kmap r covNorm allocCost treeCost * eta ≤ 1) :
    4 * covNorm * allocCost * compactRecertificationMultiplier r * Kmap * eta ≤ (1 : ℝ) / 2 ∧
      treeCost * Kmap * eta ≤ (1 : ℝ) / 2 := by
  have hallocMax :
      8 * covNorm * allocCost * compactRecertificationMultiplier r * Kmap ≤
        compactBKARHalfMarginCost Kmap r covNorm allocCost treeCost := by
    exact le_max_left _ _
  have htreeMax :
      2 * treeCost * Kmap ≤
        compactBKARHalfMarginCost Kmap r covNorm allocCost treeCost := by
    exact le_max_right _ _
  have hallocBudget := mul_le_mul_of_nonneg_right hallocMax heta
  have htreeBudget := mul_le_mul_of_nonneg_right htreeMax heta
  constructor
  · have h8 :
        (8 * covNorm * allocCost * compactRecertificationMultiplier r * Kmap) * eta ≤ 1 :=
      le_trans hallocBudget hbudget
    nlinarith
  · have h2 : (2 * treeCost * Kmap) * eta ≤ 1 :=
      le_trans htreeBudget hbudget
    nlinarith

/--
The scalar handoff used in Lemma 6.41 is strict once the base branch uses half
of a positive admission radius and the compact handoff uses at most a quarter.
-/
theorem compact_quarter_margin_closes_joint_ball
    (base compact delta : ℝ)
    (hdelta : 0 < delta)
    (hbase : base ≤ delta / 2)
    (hcompact : compact ≤ delta / 4) :
    base + compact < delta := by
  linarith

/-- A regulator-independent multiplier preserves convergence of a compact row to zero. -/
theorem fixed_multiplier_preserves_zero_limit
    (C_E : ℝ) {eta : ℕ → ℝ}
    (heta : Filter.Tendsto eta Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => C_E * eta n) Filter.atTop (nhds 0) := by
  simpa using (tendsto_const_nhds.mul heta :
    Filter.Tendsto (fun n => C_E * eta n) Filter.atTop (nhds (C_E * 0)))

#print axioms compact_recertification_multiplier_pos
#print axioms one_fixed_cost_pays_both_bkar_half_margins
#print axioms compact_quarter_margin_closes_joint_ball
#print axioms fixed_multiplier_preserves_zero_limit

end Millennium.YangMills
