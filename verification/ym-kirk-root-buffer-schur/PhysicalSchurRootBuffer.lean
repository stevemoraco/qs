import Mathlib

/-!
# Physical Schur root-buffer firewall

Finite operator-majorant bridge for the physical Yang--Mills connector.  A
Riemann-weighted Schur row acting on a bounded source root does not acquire a
factor equal to the number of lattice points in the root buffer.  A second
Riemann-weighted source on the other side is controlled by its weighted
`l1` mass.

The theorem is deliberately stated for nonnegative kernel/source majorants.
It does not prove Kirk's connector estimate, the required uniform Schur rows,
continuum convergence, Osterwalder--Schrader reconstruction, a Yang--Mills
mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills

open scoped BigOperators

/-- A weighted nonnegative row bound controls the row after insertion of any
source majorant bounded by `B`; no cardinality factor appears. -/
theorem weighted_row_applied_to_bounded_source
    {ι : Type} [Fintype ι]
    (kernel source : ι → ℝ) {w A B : ℝ}
    (hw : 0 ≤ w) (hB : 0 ≤ B)
    (hkernel : ∀ i, 0 ≤ kernel i)
    (hsource : ∀ i, source i ≤ B)
    (hrow : w * (∑ i, kernel i) ≤ A) :
    w * (∑ i, kernel i * source i) ≤ A * B := by
  have hsum :
      (∑ i, kernel i * source i) ≤ (∑ i, kernel i * B) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hsource i) (hkernel i)
  have hweighted :
      w * (∑ i, kernel i * source i) ≤
        w * (∑ i, kernel i * B) :=
    mul_le_mul_of_nonneg_left hsum hw
  calc
    w * (∑ i, kernel i * source i)
        ≤ w * (∑ i, kernel i * B) := hweighted
    _ = (w * (∑ i, kernel i)) * B := by
      rw [Finset.sum_mul]
      ring
    _ ≤ A * B := mul_le_mul_of_nonneg_right hrow hB

/-- Two-buffer finite Schur form.  A right source bounded by `B`, a uniform
right weighted row bound `A`, and a left source with weighted `l1` mass at
most `F` give a bilinear bound `F * (A * B)` independent of both finite
cardinalities. -/
theorem weighted_schur_two_buffer_le
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (kernel : ι → κ → ℝ) (left : ι → ℝ) (right : κ → ℝ)
    {wLeft wRight A F B : ℝ}
    (hwLeft : 0 ≤ wLeft) (hwRight : 0 ≤ wRight)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hkernel : ∀ i j, 0 ≤ kernel i j)
    (hleft : ∀ i, 0 ≤ left i)
    (hright : ∀ j, right j ≤ B)
    (hrow : ∀ i, wRight * (∑ j, kernel i j) ≤ A)
    (hleftMass : wLeft * (∑ i, left i) ≤ F) :
    wLeft *
        (∑ i, left i * (wRight * (∑ j, kernel i j * right j))) ≤
      F * (A * B) := by
  have hpoint : ∀ i,
      wRight * (∑ j, kernel i j * right j) ≤ A * B := by
    intro i
    exact weighted_row_applied_to_bounded_source
      (kernel := kernel i) (source := right)
      hwRight hB (hkernel i) hright (hrow i)
  have hsum :
      (∑ i, left i * (wRight * (∑ j, kernel i j * right j))) ≤
        (∑ i, left i * (A * B)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hpoint i) (hleft i)
  have hweighted :
      wLeft *
          (∑ i, left i * (wRight * (∑ j, kernel i j * right j))) ≤
        wLeft * (∑ i, left i * (A * B)) :=
    mul_le_mul_of_nonneg_left hsum hwLeft
  calc
    wLeft *
        (∑ i, left i * (wRight * (∑ j, kernel i j * right j)))
        ≤ wLeft * (∑ i, left i * (A * B)) := hweighted
    _ = (wLeft * (∑ i, left i)) * (A * B) := by
      rw [Finset.sum_mul]
      ring
    _ ≤ F * (A * B) :=
      mul_le_mul_of_nonneg_right hleftMass (mul_nonneg hA hB)

#print axioms weighted_row_applied_to_bounded_source
#print axioms weighted_schur_two_buffer_le

end Millennium.YangMills
