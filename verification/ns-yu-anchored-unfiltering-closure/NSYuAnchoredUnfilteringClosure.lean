import Mathlib

/-!
# Yu anchored multifilter unfiltering closure

Finite topology and real algebra only. These statements close one categorical
step in the filtered-vorticity route: collinearity with a possibly moving
filtered anchor is preserved under coordinatewise limits, and a nonzero limit
anchor selects an actual limiting line.

The filtered line may depend arbitrarily on the filter index. No uniform line,
uniform scalar coefficient, or uniform conditioning across filters is assumed.

This file does **not** formalize Runlong Yu's PDE estimates, vanishing of Yu's
weighted direction defect, ancient-profile extraction, mollifier convergence,
Giga--Miura's Type-I theorem, Navier--Stokes regularity, or blow-up.
-/

open Filter
open Topology

namespace NSYuAnchoredUnfilteringClosure

/-- A vanishing planar minor is closed under coordinatewise sequential limits. -/
theorem zero_minor_survives_limit
    (x y a b : ℕ → ℝ) (X Y A B : ℝ)
    (hx : Tendsto x atTop (𝓝 X))
    (hy : Tendsto y atTop (𝓝 Y))
    (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B))
    (hzero : ∀ n, x n * b n - y n * a n = 0) :
    X * B - Y * A = 0 := by
  have hlim :
      Tendsto (fun n => x n * b n - y n * a n) atTop
        (𝓝 (X * B - Y * A)) :=
    (hx.mul hb).sub (hy.mul ha)
  have heq :
      (fun n => x n * b n - y n * a n) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact hzero n
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- If every approximating vector is collinear with its corresponding anchor,
then the limiting vector is collinear with the limiting anchor. The anchor line
is allowed to move with the approximation index. -/
theorem anchored_collinearity_survives_coordinatewise_limit
    (x1 x2 x3 a1 a2 a3 : ℕ → ℝ)
    (X1 X2 X3 A1 A2 A3 : ℝ)
    (hx1 : Tendsto x1 atTop (𝓝 X1))
    (hx2 : Tendsto x2 atTop (𝓝 X2))
    (hx3 : Tendsto x3 atTop (𝓝 X3))
    (ha1 : Tendsto a1 atTop (𝓝 A1))
    (ha2 : Tendsto a2 atTop (𝓝 A2))
    (ha3 : Tendsto a3 atTop (𝓝 A3))
    (h12 : ∀ n, x1 n * a2 n - x2 n * a1 n = 0)
    (h13 : ∀ n, x1 n * a3 n - x3 n * a1 n = 0)
    (h23 : ∀ n, x2 n * a3 n - x3 n * a2 n = 0) :
    X1 * A2 - X2 * A1 = 0 ∧
      X1 * A3 - X3 * A1 = 0 ∧
      X2 * A3 - X3 * A2 = 0 := by
  constructor
  · exact zero_minor_survives_limit x1 x2 a1 a2 X1 X2 A1 A2
      hx1 hx2 ha1 ha2 h12
  constructor
  · exact zero_minor_survives_limit x1 x3 a1 a3 X1 X3 A1 A3
      hx1 hx3 ha1 ha3 h13
  · exact zero_minor_survives_limit x2 x3 a2 a3 X2 X3 A2 A3
      hx2 hx3 ha2 ha3 h23

/-- Three vanishing minors and one nonzero anchor coordinate imply membership
in the one-dimensional span of the anchor. -/
theorem zero_minors_nonzero_anchor_gives_scalar
    (x1 x2 x3 a1 a2 a3 : ℝ)
    (hanchor : a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0)
    (h12 : x1 * a2 - x2 * a1 = 0)
    (h13 : x1 * a3 - x3 * a1 = 0)
    (h23 : x2 * a3 - x3 * a2 = 0) :
    ∃ c : ℝ, x1 = c * a1 ∧ x2 = c * a2 ∧ x3 = c * a3 := by
  by_cases ha1 : a1 = 0
  · by_cases ha2 : a2 = 0
    · have ha3 : a3 ≠ 0 := by
        rcases hanchor with h | h | h
        · exact False.elim (h ha1)
        · exact False.elim (h ha2)
        · exact h
      refine ⟨x3 / a3, ?_, ?_, ?_⟩
      · field_simp [ha3]
        nlinarith [h13]
      · field_simp [ha3]
        nlinarith [h23]
      · field_simp [ha3]
    · refine ⟨x2 / a2, ?_, ?_, ?_⟩
      · field_simp [ha2]
        nlinarith [h12]
      · field_simp [ha2]
      · field_simp [ha2]
        nlinarith [h23]
  · refine ⟨x1 / a1, ?_, ?_, ?_⟩
    · field_simp [ha1]
    · field_simp [ha1]
      nlinarith [h12]
    · field_simp [ha1]
      nlinarith [h13]

/-- Complete anchored closure theorem. A sequence of filter-dependent lines
converges to one actual line whenever the filtered field and one filtered anchor
converge coordinatewise and the limit anchor is nonzero. -/
theorem anchored_line_survives_coordinatewise_limit
    (x1 x2 x3 a1 a2 a3 : ℕ → ℝ)
    (X1 X2 X3 A1 A2 A3 : ℝ)
    (hx1 : Tendsto x1 atTop (𝓝 X1))
    (hx2 : Tendsto x2 atTop (𝓝 X2))
    (hx3 : Tendsto x3 atTop (𝓝 X3))
    (ha1 : Tendsto a1 atTop (𝓝 A1))
    (ha2 : Tendsto a2 atTop (𝓝 A2))
    (ha3 : Tendsto a3 atTop (𝓝 A3))
    (h12 : ∀ n, x1 n * a2 n - x2 n * a1 n = 0)
    (h13 : ∀ n, x1 n * a3 n - x3 n * a1 n = 0)
    (h23 : ∀ n, x2 n * a3 n - x3 n * a2 n = 0)
    (hanchor : A1 ≠ 0 ∨ A2 ≠ 0 ∨ A3 ≠ 0) :
    ∃ c : ℝ, X1 = c * A1 ∧ X2 = c * A2 ∧ X3 = c * A3 := by
  have hminors := anchored_collinearity_survives_coordinatewise_limit
    x1 x2 x3 a1 a2 a3 X1 X2 X3 A1 A2 A3
    hx1 hx2 hx3 ha1 ha2 ha3 h12 h13 h23
  exact zero_minors_nonzero_anchor_gives_scalar
    X1 X2 X3 A1 A2 A3 hanchor hminors.1 hminors.2.1 hminors.2.2

/-- The nonzero limiting anchor hypothesis is essential: the zero anchor cannot
represent a nonzero limiting vector by scalar multiplication. -/
theorem zero_anchor_cannot_select_nonzero_line :
    ¬ ∃ c : ℝ,
      (1 : ℝ) = c * 0 ∧
      (0 : ℝ) = c * 0 ∧
      (0 : ℝ) = c * 0 := by
  norm_num

#print axioms zero_minor_survives_limit
#print axioms anchored_collinearity_survives_coordinatewise_limit
#print axioms zero_minors_nonzero_anchor_gives_scalar
#print axioms anchored_line_survives_coordinatewise_limit
#print axioms zero_anchor_cannot_select_nonzero_line

end NSYuAnchoredUnfilteringClosure
