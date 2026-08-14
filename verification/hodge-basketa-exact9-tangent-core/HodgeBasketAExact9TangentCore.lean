import Mathlib

/-!
Finite group-theoretic shadow of the q=1,a=8 basket-A exact-9-torsion tangent reduction.

This file does NOT formalize elliptic curves, the |3o| embedding, tangent-line geometry,
Miranda triple covers, moving A3 singularities, K3 geometry, algebraic cycles, or Hodge.
It records only the exact torsion arithmetic used by the human geometric reduction.
-/

namespace Millennium.Hodge.BasketAExact9TangentCore

private theorem nine_smul_zero (q : ZMod 9) : (9 : ZMod 9) * q = 0 := by
  have h9 : (9 : ZMod 9) = 0 := by norm_num
  rw [h9, zero_mul]

/-- In Z/9Z, an element not killed by 3 is an exact order-9 shadow. Setting
`p=4q` gives the divisor relation `2p+q=0`, the nonzero 3-torsion difference
`p-q=3q`, and shows `p` is not a flex-shadow (`3p != 0`). -/
theorem exact9_root_pair_arithmetic
    (q : ZMod 9)
    (h3 : (3 : ZMod 9) * q ≠ 0) :
    let p : ZMod 9 := 4 * q
    (2 * p + q = 0) ∧
    (p - q = 3 * q) ∧
    (3 * (p - q) = 0) ∧
    (3 * p ≠ 0) := by
  dsimp
  have h9q := nine_smul_zero q
  constructor
  · calc
      2 * (4 * q) + q = 9 * q := by ring
      _ = 0 := h9q
  constructor
  · ring
  constructor
  · calc
      3 * (4 * q - q) = 9 * q := by ring
      _ = 0 := h9q
  · intro hp
    apply h3
    calc
      3 * q = 3 * (4 * q) - 9 * q := by ring
      _ = 0 := by rw [hp, h9q]; simp

/-- The residual tangent point is distinct from the tangency point: `p=q`
would force the nonzero 3-torsion class to vanish. -/
theorem root_points_distinct
    (q : ZMod 9)
    (h3 : (3 : ZMod 9) * q ≠ 0) :
    4 * q ≠ q := by
  intro h
  apply h3
  calc
    (3 : ZMod 9) * q = 4 * q - q := by ring
    _ = 0 := sub_eq_zero.mpr h

/-- The difference `p-q=3q` is a nonzero 3-torsion class. -/
theorem difference_is_nonzero_three_torsion
    (q : ZMod 9)
    (h3 : (3 : ZMod 9) * q ≠ 0) :
    let delta : ZMod 9 := 3 * q
    delta ≠ 0 ∧ 3 * delta = 0 := by
  dsimp
  refine ⟨h3, ?_⟩
  calc
    3 * (3 * q) = 9 * q := by ring
    _ = 0 := nine_smul_zero q

#print axioms exact9_root_pair_arithmetic
#print axioms root_points_distinct
#print axioms difference_is_nonzero_three_torsion

end Millennium.Hodge.BasketAExact9TangentCore
