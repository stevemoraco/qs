import Mathlib

/-!
# B229 finite two-layer / edge-TV repair algebra

This file formalizes only the load-bearing scalar facts behind B229:

* the reciprocal-Haar three-point stencil is one difference after the fixed
  preconditioner;
* any nonpositive repaired edge pays at least the positive edge debt;
* the canonical nonpositive repair attains that debt exactly;
* a selector in `[0,1]` cannot exceed the positive part and the sign selector
  attains it exactly;
* the four-edge positive mass is exactly one half of edge total variation plus
  endpoint drift.

It does **not** formalize quarter-block integration, bounded-variation
quadrature, prime sums, PNT, Mellin/Landau, zeta, Xi, Deng--Yang--Lu, B46, RH,
or not-RH.
-/

namespace RHB229TwoLayerTVRepairFinite

/-- Continuous-time B229 uses the same scalar factorization as B227. -/
theorem preconditioner_factor (c mPrev m mNext : ℝ) :
    c * mNext - (1 + c) * m + mPrev =
      (c * mNext - m) - (c * m - mPrev) := by
  ring

/-- If a repaired edge is constrained to be nonpositive, its absolute repair
cost dominates the original positive edge debt. -/
theorem positive_part_le_abs_repair (d e : ℝ) (he : e ≤ 0) :
    max d 0 ≤ |d - e| := by
  by_cases hd : 0 ≤ d
  · rw [max_eq_left hd]
    have hed : e ≤ d := le_trans he hd
    have hde : 0 ≤ d - e := sub_nonneg.mpr hed
    rw [abs_of_nonneg hde]
    linarith
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_right hd']
    exact abs_nonneg _

/-- The canonical monotone edge repair `min d 0` attains the positive-part
cost exactly. -/
theorem canonical_edge_repair (d : ℝ) :
    |d - min d 0| = max d 0 := by
  by_cases hd : d ≤ 0
  · rw [min_eq_left hd, max_eq_right hd]
    simp
  · have h0d : 0 ≤ d := le_of_not_ge hd
    rw [min_eq_right h0d, max_eq_left h0d]
    simp [abs_of_nonneg h0d]

/-- Every scalar selector in `[0,1]` is bounded by the positive part. -/
theorem selector_upper (d phi : ℝ) (h0 : 0 ≤ phi) (h1 : phi ≤ 1) :
    phi * d ≤ max d 0 := by
  by_cases hd : 0 ≤ d
  · rw [max_eq_left hd]
    have h := mul_le_mul_of_nonneg_right h1 hd
    simpa using h
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_right hd']
    exact mul_nonpos_of_nonneg_of_nonpos h0 hd'

/-- The sign selector attains the positive part exactly. -/
theorem selector_exact (d : ℝ) :
    max d 0 = (if 0 ≤ d then (1 : ℝ) else 0) * d := by
  by_cases hd : 0 ≤ d
  · simp [hd, max_eq_left hd]
  · have hd' : d ≤ 0 := le_of_not_ge hd
    simp [hd, max_eq_right hd']

/-- Four independent nonpositive repaired edges dominate the four-edge
positive mass. -/
theorem four_edge_repair_lower
    (d0 d1 d2 d3 e0 e1 e2 e3 : ℝ)
    (he0 : e0 ≤ 0) (he1 : e1 ≤ 0) (he2 : e2 ≤ 0) (he3 : e3 ≤ 0) :
    max d0 0 + max d1 0 + max d2 0 + max d3 0 ≤
      |d0 - e0| + |d1 - e1| + |d2 - e2| + |d3 - e3| := by
  have h0 := positive_part_le_abs_repair d0 e0 he0
  have h1 := positive_part_le_abs_repair d1 e1 he1
  have h2 := positive_part_le_abs_repair d2 e2 he2
  have h3 := positive_part_le_abs_repair d3 e3 he3
  linarith

/-- The canonical edgewise repair attains the four-edge lower bound exactly. -/
theorem four_edge_canonical_repair_exact (d0 d1 d2 d3 : ℝ) :
    max d0 0 + max d1 0 + max d2 0 + max d3 0 =
      |d0 - min d0 0| + |d1 - min d1 0| +
      |d2 - min d2 0| + |d3 - min d3 0| := by
  rw [canonical_edge_repair d0, canonical_edge_repair d1,
      canonical_edge_repair d2, canonical_edge_repair d3]

/-- Scalar Jordan identity for the positive part. -/
theorem positive_part_abs_identity (d : ℝ) :
    max d 0 = (|d| + d) / 2 := by
  by_cases hd : 0 ≤ d
  · rw [max_eq_left hd, abs_of_nonneg hd]
    ring
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_right hd', abs_of_nonpos hd']
    ring

/-- The four-edge one-sided mass equals one half of edge total variation plus
net endpoint drift (the sum of the four edge increments). -/
theorem four_edge_tv_endpoint_identity (d0 d1 d2 d3 : ℝ) :
    max d0 0 + max d1 0 + max d2 0 + max d3 0 =
      (|d0| + |d1| + |d2| + |d3| + (d0 + d1 + d2 + d3)) / 2 := by
  rw [positive_part_abs_identity d0, positive_part_abs_identity d1,
      positive_part_abs_identity d2, positive_part_abs_identity d3]
  ring

#print axioms preconditioner_factor
#print axioms positive_part_le_abs_repair
#print axioms canonical_edge_repair
#print axioms selector_upper
#print axioms selector_exact
#print axioms four_edge_repair_lower
#print axioms four_edge_canonical_repair_exact
#print axioms positive_part_abs_identity
#print axioms four_edge_tv_endpoint_identity

end RHB229TwoLayerTVRepairFinite
