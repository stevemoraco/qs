import Mathlib

namespace NSChildTwoResponseDeterminantFinite

/-!
Finite real-algebra shadow of the dual-purpose child-shell determinant gate.

The human theorem interprets the two rows as parent-correction and child-response
coordinates of two signed packet channels.  This file does not define Fourier
packets, helicity, localization, Leray projection, shell capacities,
Navier--Stokes solutions, or blow-up.
-/

/-- Determinant of the two response rows. -/
def det2 (p1 p2 c1 c2 : ℝ) : ℝ := p1 * c2 - p2 * c1

/-- First Cramer coefficient for parent target `r` and child target zero. -/
noncomputable def repairX (r p1 p2 c1 c2 : ℝ) : ℝ :=
  r * c2 / det2 p1 p2 c1 c2

/-- Second Cramer coefficient for parent target `r` and child target zero. -/
noncomputable def repairY (r p1 p2 c1 c2 : ℝ) : ℝ :=
  -r * c1 / det2 p1 p2 c1 c2

/-- Nonzero determinant gives exact parent repair. -/
theorem exact_parent_repair
    {r p1 p2 c1 c2 : ℝ}
    (hdet : det2 p1 p2 c1 c2 ≠ 0) :
    p1 * repairX r p1 p2 c1 c2 +
      p2 * repairY r p1 p2 c1 c2 = r := by
  unfold repairX repairY
  field_simp [hdet]
  unfold det2
  ring

/-- The same Cramer coefficients preserve the child response exactly. -/
theorem exact_child_neutrality
    {r p1 p2 c1 c2 : ℝ}
    (hdet : det2 p1 p2 c1 c2 ≠ 0) :
    c1 * repairX r p1 p2 c1 c2 +
      c2 * repairY r p1 p2 c1 c2 = 0 := by
  unfold repairX repairY
  field_simp [hdet]
  ring

/-- If the determinant vanishes and the first child response is nonzero, every
child-neutral combination is also parent-neutral. -/
theorem singular_first_child_blocks_parent_repair
    {p1 p2 c1 c2 x y : ℝ}
    (hdet : det2 p1 p2 c1 c2 = 0)
    (hc1 : c1 ≠ 0)
    (hchild : c1 * x + c2 * y = 0) :
    p1 * x + p2 * y = 0 := by
  have hid :
      c1 * (p1 * x + p2 * y) -
          p1 * (c1 * x + c2 * y) =
        -det2 p1 p2 c1 c2 * y := by
    unfold det2
    ring
  rw [hdet, hchild] at hid
  have hmul : c1 * (p1 * x + p2 * y) = 0 := by
    simpa using hid
  exact (mul_eq_zero.mp hmul).resolve_left hc1

/-- Symmetric singular obstruction when the second child response is nonzero. -/
theorem singular_second_child_blocks_parent_repair
    {p1 p2 c1 c2 x y : ℝ}
    (hdet : det2 p1 p2 c1 c2 = 0)
    (hc2 : c2 ≠ 0)
    (hchild : c1 * x + c2 * y = 0) :
    p1 * x + p2 * y = 0 := by
  have hid :
      c2 * (p1 * x + p2 * y) -
          p2 * (c1 * x + c2 * y) =
        det2 p1 p2 c1 c2 * x := by
    unfold det2
    ring
  rw [hdet, hchild] at hid
  have hmul : c2 * (p1 * x + p2 * y) = 0 := by
    simpa using hid
  exact (mul_eq_zero.mp hmul).resolve_left hc2

/-- Exact six-term determinant perturbation identity. -/
theorem determinant_perturbation_identity
    (p1 p2 c1 c2 e11 e12 e21 e22 : ℝ) :
    det2 (p1 + e11) (p2 + e12) (c1 + e21) (c2 + e22) -
        det2 p1 p2 c1 c2 =
      p1 * e22 + e11 * c2 + e11 * e22 -
        p2 * e21 - e12 * c1 - e12 * e21 := by
  unfold det2
  ring

/-- Reverse-triangle transfer from a base determinant lower bound and an
absolute perturbation bound. -/
theorem abs_lower_of_perturbation
    {base pert delta err : ℝ}
    (hbase : delta ≤ |base|)
    (herr : |pert - base| ≤ err) :
    delta - err ≤ |pert| := by
  have htri : |base| ≤ |pert| + |base - pert| := by
    calc
      |base| = |pert + (base - pert)| := by ring_nf
      _ ≤ |pert| + |base - pert| := abs_add _ _
  rw [abs_sub_comm] at htri
  linarith

/-- A principal determinant lower bound survives any perturbation whose
absolute determinant error is smaller than that lower bound. -/
theorem determinant_stability_from_error_bound
    {base pert H delta C eta : ℝ}
    (hbase : delta * H ^ 2 ≤ |base|)
    (herr : |pert - base| ≤
      (4 * C * eta + 2 * eta ^ 2) * H ^ 2) :
    (delta - 4 * C * eta - 2 * eta ^ 2) * H ^ 2 ≤ |pert| := by
  have h := abs_lower_of_perturbation hbase herr
  nlinarith

/-- One Cramer component is small when the target is small relative to the
response scale and the normalized determinant is bounded below. -/
theorem cramer_component_bound
    {r c Delta C V H delta : ℝ}
    (hH : 0 < H)
    (hdelta : 0 < delta)
    (hC : 0 ≤ C)
    (hV : 0 ≤ V)
    (hr : |r| ≤ V)
    (hc : |c| ≤ C * H)
    (hdet : delta * H ^ 2 ≤ |Delta|) :
    |r * c / Delta| ≤ (C / delta) * (V / H) := by
  have hden : 0 < delta * H ^ 2 :=
    mul_pos hdelta (sq_pos_of_pos hH)
  have hnum : |r| * |c| ≤ V * (C * H) := by
    exact mul_le_mul hr hc (abs_nonneg c) hV
  rw [abs_div, abs_mul]
  calc
    |r| * |c| / |Delta| ≤ V * (C * H) / |Delta| := by
      exact div_le_div_of_nonneg_right hnum (abs_nonneg Delta)
    _ ≤ V * (C * H) / (delta * H ^ 2) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg hV (mul_nonneg hC (le_of_lt hH))) hden hdet
    _ = (C / delta) * (V / H) := by
      field_simp [ne_of_gt hH, ne_of_gt hdelta]
      ring

/-- The exact neutral repair uses only `O(V/H)` total signed coefficient mass. -/
theorem cramer_pair_budget
    {r p1 p2 c1 c2 C V H delta : ℝ}
    (hH : 0 < H)
    (hdelta : 0 < delta)
    (hC : 0 ≤ C)
    (hV : 0 ≤ V)
    (hr : |r| ≤ V)
    (hc1 : |c1| ≤ C * H)
    (hc2 : |c2| ≤ C * H)
    (hdet : delta * H ^ 2 ≤ |det2 p1 p2 c1 c2|) :
    |repairX r p1 p2 c1 c2| +
        |repairY r p1 p2 c1 c2| ≤
      (2 * C / delta) * (V / H) := by
  have hx := cramer_component_bound hH hdelta hC hV hr hc2 hdet
  have hy := cramer_component_bound hH hdelta hC hV hr hc1 hdet
  unfold repairX repairY
  rw [abs_div, abs_mul, abs_neg, abs_div, abs_mul, abs_neg] at ⊢
  nlinarith

/-- Nonnegative coefficients are a genuinely stronger requirement: even an
invertible response matrix need not reach a target outside its positive cone. -/
theorem determinant_not_sufficient_for_positive_cone :
    det2 1 0 0 1 ≠ 0 ∧
      ¬ ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
        1 * x + 0 * y = -1 ∧ 0 * x + 1 * y = 0 := by
  constructor
  · norm_num [det2]
  · rintro ⟨x, y, hx, hy, hparent, hchild⟩
    norm_num at hparent hchild
    linarith

#print axioms exact_parent_repair
#print axioms exact_child_neutrality
#print axioms singular_first_child_blocks_parent_repair
#print axioms singular_second_child_blocks_parent_repair
#print axioms determinant_perturbation_identity
#print axioms abs_lower_of_perturbation
#print axioms determinant_stability_from_error_bound
#print axioms cramer_component_bound
#print axioms cramer_pair_budget
#print axioms determinant_not_sufficient_for_positive_cone

end NSChildTwoResponseDeterminantFinite
