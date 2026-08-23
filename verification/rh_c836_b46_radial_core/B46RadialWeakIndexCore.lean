import Mathlib

/-!
# RH C833 finite B46 radial / weak-index core

Historical namespace label `C833` is retained for provenance; the companion
human theorem was authoritatively retyped RH C836 after a post-commit label
collision sweep.

This file formalizes only finite real algebra used by that theorem:

* the positive three-tent cap packaging;
* the exact reduction from the two-positive form to the three-translate B46 row;
* the normalized weighted slope-defect identity;
* the exact hostile boundary atom where the center tent vanishes but the cap is positive;
* one scalar weighted shifted-index domination inequality.

It does not formalize prime powers, von Mangoldt weights, Stieltjes integration,
Suzuki's explicit formula, B329/B336, Zeta23/BGST, zeta zeros, or RH.
-/

namespace Millennium
namespace RH
namespace C833

/-- Positive triangular kernel. -/
noncomputable def tent (h u : ℝ) : ℝ := max (h - |u|) 0

/-- The positive cap written as three neighboring tents. -/
noncomputable def cap (h u : ℝ) : ℝ :=
  tent h (u + h) + tent h u + tent h (u - h)

/-- Algebraic B46 row after the radial positive decomposition. -/
noncomputable def radialRow (h c u : ℝ) : ℝ :=
  (1 + c + c^2) * tent h u - c * cap h u

/-- Expanding the positive cap leaves the familiar three-translate B46 stencil. -/
theorem radialRow_threeTranslate (h c u : ℝ) :
    radialRow h c u =
      (1 + c^2) * tent h u - c * (tent h (u + h) + tent h (u - h)) := by
  simp [radialRow, cap]
  ring

/-- The normalized B46 stencil is a weighted defect of consecutive slopes. -/
theorem normalizedSlopeDefect (c sm s sp : ℝ) :
    (1 + c^2) * s - sm - c^2 * sp
      = (s - sm) - c^2 * (sp - s) := by
  ring

/-- A tent centered one radius away vanishes exactly at the boundary. -/
theorem tent_at_radius {h : ℝ} (hh : 0 ≤ h) : tent h h = 0 := by
  rw [tent, abs_of_nonneg hh]
  simp

/-- The cap remains positive at the same boundary: its value is exactly `h`. -/
theorem cap_at_radius {h : ℝ} (hh : 0 ≤ h) : cap h h = h := by
  have h2 : 0 ≤ h + h := add_nonneg hh hh
  have hneg : h - (h + h) ≤ 0 := by linarith
  rw [cap]
  simp [tent, abs_of_nonneg hh, abs_of_nonneg h2, hneg, hh]

/-- The exact B46 radial value at the positive-cone hostile boundary. -/
theorem radialRow_boundary_value
    {h c : ℝ} (hh : 0 ≤ h) :
    radialRow h c h = -c * h := by
  rw [radialRow, tent_at_radius hh, cap_at_radius hh]
  ring

/-- The B46 radial row is strictly negative on a positive boundary atom. -/
theorem radialRow_boundary_negative
    {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    radialRow h c h < 0 := by
  rw [radialRow_boundary_value (le_of_lt hh)]
  exact neg_neg_of_pos (mul_pos hc hh)

/-- Hence no finite pointwise domination `cap ≤ K * tent` can hold on the
positive cone when `h>0`: it already fails at the boundary atom. -/
theorem no_pointwise_cap_by_tent
    {h K : ℝ} (hh : 0 < h) :
    ¬ cap h h ≤ K * tent h h := by
  have hh0 : 0 ≤ h := le_of_lt hh
  rw [cap_at_radius hh0, tent_at_radius hh0]
  simpa using (not_le_of_gt hh)

/-- One scalar weighted shifted-index contribution is dominated by the
corresponding weighted negative depth. -/
theorem weightedShift_le_depth
    {w lam depth : ℝ}
    (hw : 0 ≤ w) (hcross : lam ≤ depth) :
    lam * w ≤ depth * w := by
  exact mul_le_mul_of_nonneg_right hcross hw

#print axioms radialRow_threeTranslate
#print axioms normalizedSlopeDefect
#print axioms tent_at_radius
#print axioms cap_at_radius
#print axioms radialRow_boundary_value
#print axioms radialRow_boundary_negative
#print axioms no_pointwise_cap_by_tent
#print axioms weightedShift_le_depth

end C833
end RH
end Millennium
