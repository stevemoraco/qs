import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 compact/BKAR norm-embedding firewall

The compact row printed as (99) is weighted by a diameter exponent, whereas the
permanent weak rooted space used upstream is weighted by a spanning-tree/support
cost.  This file formalizes the scalar square-grid obstruction to deriving a
uniform tree-exponent row from a diameter-exponent row with only one fixed
multiplicative conversion constant.

For a `k × k` separated-terminal proxy, use

* diameter proxy `2 (k - 1)`;
* tree/support proxy `k^2 - 1`.

The statements below are finite real algebra only.  They do not assert that
Kirk's actual compact activities realize this hostile geometry, nor do they
formalize either rooted Banach norm.  They are a firewall: any source proof of a
uniform embedding must use additional structure beyond the two displayed scalar
weights.
-/

/-- Once the square-grid side length is large enough, a positive tree exponent
beats any fixed diameter exponent plus any fixed additive log-constant. -/
theorem square_grid_tree_exponent_beats_diameter
    (κ m B k : ℝ)
    (hκ : 0 < κ)
    (hm : 0 ≤ m)
    (hk : 1 < k)
    (hlarge : 2 * m + |B| + 1 < κ * (k - 1)) :
    m * (2 * (k - 1)) + B < κ * (k^2 - 1) := by
  have hx : 0 < k - 1 := by linarith
  have hmul := mul_lt_mul_of_pos_right hlarge hx
  have hB : B ≤ |B| := le_abs_self B
  nlinarith [hmul]

/-- For every positive tree exponent, every nonnegative diameter exponent, and
every fixed additive conversion budget `B`, there is a hostile square-grid side
length.  Equivalently, no fixed multiplicative norm-conversion constant can
turn a pure diameter exponential row into the stronger tree exponential row on
this family. -/
theorem no_uniform_square_grid_exponential_embedding
    (κ m B : ℝ)
    (hκ : 0 < κ)
    (hm : 0 ≤ m) :
    ∃ k : ℝ,
      1 < k ∧
      m * (2 * (k - 1)) + B < κ * (k^2 - 1) := by
  let A : ℝ := 2 * m + |B| + 2
  let k : ℝ := A / κ + 2
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [abs_nonneg B]
  have hdiv : 0 < A / κ := div_pos hA hκ
  have hk : 1 < k := by
    dsimp [k]
    linarith
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hcancel : κ * (A / κ) = A := by
    field_simp [hκne]
  have hlarge : 2 * m + |B| + 1 < κ * (k - 1) := by
    dsimp [k]
    rw [show A / κ + 2 - 1 = A / κ + 1 by ring]
    rw [mul_add, hcancel]
    dsimp [A]
    nlinarith
  exact ⟨k, hk,
    square_grid_tree_exponent_beats_diameter κ m B k hκ hm hk hlarge⟩

#print axioms square_grid_tree_exponent_beats_diameter
#print axioms no_uniform_square_grid_exponential_embedding

end Millennium.YangMills
