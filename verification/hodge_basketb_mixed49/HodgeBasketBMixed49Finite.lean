import Mathlib

namespace HodgeBasketBMixed49Finite

/-- The mixed branch's two-vertex intersection matrix has determinant two. -/
theorem mixed_graph_determinant :
    (-1 : ℤ) * (-3) - 1 * 1 = 2 := by
  norm_num

/-- The candidate fundamental cycle `(1,1)` is anti-nef on the graph
`F(-1,g=1)-E(-3)`. -/
theorem fundamental_cycle_intersections :
    ((-1 : ℤ) * 1 + 1 * 1 = 0) ∧
    (1 * 1 + (-3 : ℤ) * 1 = -2) := by
  norm_num

/-- The integral vector `(2,1)` solves the canonical intersection equations. -/
theorem canonical_cycle_intersections :
    ((-1 : ℤ) * 2 + 1 * 1 = -1) ∧
    (1 * 2 + (-3 : ℤ) * 1 = -1) := by
  norm_num

/-- The length-two elliptic-sequence vectors add to the canonical vector. -/
theorem elliptic_sequence_sum :
    ((1 : ℤ) + 1 = 2) ∧ ((1 : ℤ) + 0 = 1) := by
  norm_num

/-- Abstract line-bundle cancellation: if the normal class and exceptional
point class cancel, then the obstruction class `-(N+P)` is trivial. -/
theorem obstruction_class_trivial
    {A : Type*} [AddCommGroup A] (N P : A)
    (hcancel : N + P = 0) :
    -(N + P) = 0 := by
  rw [hcancel]
  simp

/-- A local geometric-genus contribution two cannot fit inside a total q-budget
of one. -/
theorem pg_two_contradicts_q_one
    (localPg totalQ : Nat)
    (hlocal : localPg = 2)
    (htotal : totalQ = 1)
    (hle : localPg ≤ totalQ) :
    False := by
  omega

/-- Logical terminal composition: if every stationary-nonnormal survivor must
enter the mixed branch and the mixed branch is impossible, then the stationary
nonnormal branch is impossible. -/
theorem stationary_nonnormal_eliminated
    (StationaryNonnormal Mixed49 : Prop)
    (htoMixed : StationaryNonnormal → Mixed49)
    (hkill : ¬ Mixed49) :
    ¬ StationaryNonnormal := by
  intro h
  exact hkill (htoMixed h)

#print axioms HodgeBasketBMixed49Finite.mixed_graph_determinant
#print axioms HodgeBasketBMixed49Finite.fundamental_cycle_intersections
#print axioms HodgeBasketBMixed49Finite.canonical_cycle_intersections
#print axioms HodgeBasketBMixed49Finite.elliptic_sequence_sum
#print axioms HodgeBasketBMixed49Finite.obstruction_class_trivial
#print axioms HodgeBasketBMixed49Finite.pg_two_contradicts_q_one
#print axioms HodgeBasketBMixed49Finite.stationary_nonnormal_eliminated

end HodgeBasketBMixed49Finite
