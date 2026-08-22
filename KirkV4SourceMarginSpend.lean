import Mathlib

namespace Millennium.YangMills

/-!
# Explicitly spend a Cauchy source tail inside a strict margin

This file is the scalar bridge between an analytic tail estimate

  tail(r) <= C (r/rho) / (1-r/rho)

and a strict admission or contraction margin `delta > 0`. It chooses one
concrete positive radius and proves that the tail fits the margin.

No polymer geometry, Yang--Mills measure, mass gap, or Clay conclusion is
encoded here.
-/

/-- Fraction of the original source tube sufficient to pay margin `delta`. -/
noncomputable def sourceMarginRatio (C delta : ℝ) : ℝ :=
  delta / (2 * (C + delta))

/-- Concrete source radius at the margin ratio. -/
noncomputable def sourceMarginRadius (rho C delta : ℝ) : ℝ :=
  rho * sourceMarginRatio C delta

/-- The explicit margin ratio is positive. -/
theorem sourceMarginRatio_pos
    (C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    0 < sourceMarginRatio C delta := by
  unfold sourceMarginRatio
  have hsum : 0 < C + delta := by linarith
  positivity

/-- The explicit margin ratio is strictly below one. -/
theorem sourceMarginRatio_lt_one
    (C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    sourceMarginRatio C delta < 1 := by
  unfold sourceMarginRatio
  have hden : 0 < 2 * (C + delta) := by linarith
  exact (div_lt_one hden).2 (by linarith)

/-- The geometric tail at the explicit ratio is strictly below the requested
margin. -/
theorem sourceMarginRatio_tail_lt
    (C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    C * sourceMarginRatio C delta /
        (1 - sourceMarginRatio C delta) < delta := by
  let q := sourceMarginRatio C delta
  have hq1 : q < 1 := sourceMarginRatio_lt_one C delta hC hdelta
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  apply (div_lt_iff₀ hden).2
  have hsum : 0 < C + delta := by linarith
  have hhalf : q * (C + delta) = delta / 2 := by
    dsimp [q, sourceMarginRatio]
    field_simp [ne_of_gt hsum]
  nlinarith

/-- The concrete source radius is positive. -/
theorem sourceMarginRadius_pos
    (rho C delta : ℝ)
    (hrho : 0 < rho)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    0 < sourceMarginRadius rho C delta := by
  unfold sourceMarginRadius
  exact mul_pos hrho (sourceMarginRatio_pos C delta hC hdelta)

/-- The concrete source radius lies strictly inside the original source tube. -/
theorem sourceMarginRadius_lt_tube
    (rho C delta : ℝ)
    (hrho : 0 < rho)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta) :
    sourceMarginRadius rho C delta < rho := by
  unfold sourceMarginRadius
  simpa using mul_lt_mul_of_pos_left
    (sourceMarginRatio_lt_one C delta hC hdelta) hrho

/-- Dividing the concrete radius by the tube radius recovers the margin ratio. -/
theorem sourceMarginRadius_div_tube
    (rho C delta : ℝ)
    (hrho : 0 < rho) :
    sourceMarginRadius rho C delta / rho = sourceMarginRatio C delta := by
  unfold sourceMarginRadius
  field_simp [ne_of_gt hrho]

/-- Any scalar tail under the geometric Cauchy majorant fits the margin at the
explicit ratio. -/
theorem abstract_tail_fits_margin_at_ratio
    (tail C delta : ℝ)
    (hC : 0 ≤ C)
    (hdelta : 0 < delta)
    (htail : tail ≤
      C * sourceMarginRatio C delta /
        (1 - sourceMarginRatio C delta)) :
    tail < delta := by
  exact htail.trans_lt (sourceMarginRatio_tail_lt C delta hC hdelta)

/-- A tail function satisfying the geometric Cauchy majorant on the source tube
has one explicit positive radius at which it fits any prescribed strict
margin. -/
theorem exists_source_radius_paying_abstract_tail
    (tail : ℝ → ℝ)
    (C rho delta : ℝ)
    (hC : 0 ≤ C)
    (hrho : 0 < rho)
    (hdelta : 0 < delta)
    (htail : ∀ r : ℝ, 0 ≤ r → r < rho →
      tail r ≤ C * (r / rho) / (1 - r / rho)) :
    ∃ r : ℝ, 0 < r ∧ r < rho ∧ tail r < delta := by
  let r := sourceMarginRadius rho C delta
  have hr : 0 < r := sourceMarginRadius_pos rho C delta hrho hC hdelta
  have hrrho : r < rho :=
    sourceMarginRadius_lt_tube rho C delta hrho hC hdelta
  refine ⟨r, hr, hrrho, ?_⟩
  have hbound := htail r hr.le hrrho
  have hratio : r / rho = sourceMarginRatio C delta := by
    exact sourceMarginRadius_div_tube rho C delta hrho
  rw [hratio] at hbound
  exact abstract_tail_fits_margin_at_ratio
    (tail r) C delta hC hdelta hbound

#print axioms sourceMarginRatio_pos
#print axioms sourceMarginRatio_lt_one
#print axioms sourceMarginRatio_tail_lt
#print axioms sourceMarginRadius_pos
#print axioms sourceMarginRadius_lt_tube
#print axioms sourceMarginRadius_div_tube
#print axioms abstract_tail_fits_margin_at_ratio
#print axioms exists_source_radius_paying_abstract_tail

end Millennium.YangMills
