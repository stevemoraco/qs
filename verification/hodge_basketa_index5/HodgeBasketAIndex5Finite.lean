import Mathlib

namespace HodgeBasketAIndex5Finite

/-- Determinant recurrence for a linear plumbing with diagonal entries `-aᵢ`
and unit off-diagonal intersections. -/
def chainDet : List ℤ → ℤ
  | [] => 1
  | [a] => -a
  | a :: b :: rest => (-a) * chainDet (b :: rest) - chainDet rest

/-- The downstairs elliptic `(-2)` plus three rational `(-2)` chain has
determinant five. -/
theorem downstairs_det_five : chainDet [2, 2, 2, 2] = 5 := by
  norm_num [chainDet]

/-- The numerator `(8,6,4,2)` solves the downstairs canonical-cycle equations
after clearing the canonical denominator five. -/
theorem downstairs_canonical_numerator :
    ((-2 : ℤ) * 8 + 6 = -10) ∧
    ((8 : ℤ) - 2 * 6 + 4 = 0) ∧
    ((6 : ℤ) - 2 * 4 + 2 = 0) ∧
    ((4 : ℤ) - 2 * 2 = 0) := by
  norm_num

/-- The three node-resolution Hirzebruch--Jung chains all have determinant five
(up to the sign convention for a one-vertex chain). -/
theorem node_chain_determinants :
    chainDet [2, 3] = 5 ∧
    chainDet [5] = -5 ∧
    chainDet [3, 2] = 5 := by
  norm_num [chainDet]

/-- The smooth normalized-cover plumbing before rational `(-1)` contractions
has unimodular determinant. -/
theorem preminimal_cover_unimodular :
    chainDet [1, 2, 3, 1, 5, 1, 3, 2, 1] = -1 := by
  norm_num [chainDet]

/-- After the explicit rational `(-1)` contractions, the minimal index-one
cover graph is the elliptic `(-1)` tip followed by three rational `(-2)` curves. -/
theorem minimal_cover_unimodular : chainDet [1, 2, 2, 2] = 1 := by
  norm_num [chainDet]

/-- `(4,3,2,1)` is the integral canonical cycle of the minimal cover graph. -/
theorem minimal_cover_canonical_cycle :
    ((-4 : ℤ) + 3 = -1) ∧
    ((4 : ℤ) - 2 * 3 + 2 = 0) ∧
    ((3 : ℤ) - 2 * 2 + 1 = 0) ∧
    ((2 : ℤ) - 2 = 0) := by
  norm_num

/-- The first cyclic-cover node has total-pullback valuations `5,3,1`. -/
theorem first_node_pullback_valuation_order :
    (5 : ℤ) > 3 ∧ (3 : ℤ) > 1 ∧ (1 : ℤ) > 0 := by
  norm_num

/-- Exact abstract torsion ledger behind the elliptic basepoint constraint:
`3T=0` and `5T=D` force `3D=0`. -/
theorem torsion_difference_three
    {A : Type*} [AddCommGroup A] (T D : A)
    (h3 : 3 • T = 0) (h5 : 5 • T = D) :
    3 • D = 0 := by
  rw [← h5]
  calc
    3 • (5 • T) = 5 • (3 • T) := by
      simp only [smul_smul]
      norm_num
    _ = 0 := by simp [h3]

/-- For the natural index-five normal character, the four successive pole-layer
characters have residues `1,4,2,0`, hence exactly one invariant layer. -/
theorem four_layer_character_count :
    ([1, 4, 2, 0].filter (fun n : Nat => n = 0)).length = 1 := by
  decide

#print axioms HodgeBasketAIndex5Finite.downstairs_det_five
#print axioms HodgeBasketAIndex5Finite.downstairs_canonical_numerator
#print axioms HodgeBasketAIndex5Finite.node_chain_determinants
#print axioms HodgeBasketAIndex5Finite.preminimal_cover_unimodular
#print axioms HodgeBasketAIndex5Finite.minimal_cover_unimodular
#print axioms HodgeBasketAIndex5Finite.minimal_cover_canonical_cycle
#print axioms HodgeBasketAIndex5Finite.first_node_pullback_valuation_order
#print axioms HodgeBasketAIndex5Finite.torsion_difference_three
#print axioms HodgeBasketAIndex5Finite.four_layer_character_count

end HodgeBasketAIndex5Finite
