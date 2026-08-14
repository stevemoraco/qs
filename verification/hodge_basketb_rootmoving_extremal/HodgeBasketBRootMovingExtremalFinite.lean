import Mathlib

namespace HodgeBasketBRootMovingExtremalFinite

/-- The q1a8 pencil class `D = 3R + 6e` has zero intersection with `R`
and degree three on an elliptic fibre in the lattice `R^2=-2`, `R.e=1`,
`e^2=0`. -/
theorem ns_intersection_ledger :
    ((3 : ℤ) * (-2) + 6 * 1 = 0) ∧
    ((3 : ℤ) * 1 + 6 * 0 = 3) := by
  norm_num

/-- After removing a maximal `k`-fold elliptic-fibre component, the residual
class `3R + (6-k)e` has intersection `-k` with `R`. -/
theorem residual_intersection (k : ℤ) :
    3 * (-2) + (6 - k) * 1 = -k := by
  ring

/-- An element killed by both two and three is zero. This is the finite group
shadow used to separate exact nonzero three-torsion from two-torsion. -/
theorem two_and_three_torsion_is_zero
    {G : Type*} [AddCommGroup G] (x : G)
    (h2 : x + x = 0)
    (h3 : x + x + x = 0) :
    x = 0 := by
  calc
    x = (x + x + x) - (x + x) := by abel
    _ = 0 - 0 := by rw [h3, h2]
    _ = 0 := by simp

/-- Therefore a nonzero element satisfying the three-torsion relation cannot
satisfy the two-torsion relation. -/
theorem nonzero_three_torsion_not_two_torsion
    {G : Type*} [AddCommGroup G] (x : G)
    (hx : x ≠ 0)
    (h3 : x + x + x = 0) :
    x + x ≠ 0 := by
  intro h2
  exact hx (two_and_three_torsion_is_zero x h2 h3)

/-- The scalar root-moving squeeze: the effective-cone and weight-two-child
ledger leave only `k=5` or `k=6`; the fivefold branch can carry at most two
unit root points, while a moving `A3` needs at least three. -/
theorem root_moving_forces_six
    (k h : Nat)
    (hk : k = 5 ∨ k = 6)
    (hmoving : 3 ≤ h)
    (hfive : k = 5 → h ≤ 2) :
    k = 6 := by
  rcases hk with rfl | h6
  · omega
  · exact h6

/-- Once the sixfold special member excludes every off-root unit basepoint,
all five unit basket points lie over the root. -/
theorem no_offroot_units_forces_all_five
    (h offroot : Nat)
    (htotal : h + offroot = 5)
    (hoffroot : offroot = 0) :
    h = 5 := by
  omega

/-- Finite terminal composition of the root-moving resource ledger. The
geometric hypotheses that produce `hk`, `hfive`, and `hoffroot` are deliberately
kept explicit rather than hidden in this arithmetic theorem. -/
theorem root_moving_extremal
    (k h offroot alphaOrder : Nat)
    (hk : k = 5 ∨ k = 6)
    (hmoving : 3 ≤ h)
    (hfive : k = 5 → h ≤ 2)
    (htotal : h + offroot = 5)
    (hoffroot : k = 6 → offroot = 0)
    (halpha : h = 5 → alphaOrder = 13) :
    k = 6 ∧ h = 5 ∧ alphaOrder = 13 := by
  have hk6 : k = 6 := root_moving_forces_six k h hk hmoving hfive
  have hoff0 : offroot = 0 := hoffroot hk6
  have hh5 : h = 5 := no_offroot_units_forces_all_five h offroot htotal hoff0
  exact ⟨hk6, hh5, halpha hh5⟩

#print axioms HodgeBasketBRootMovingExtremalFinite.ns_intersection_ledger
#print axioms HodgeBasketBRootMovingExtremalFinite.residual_intersection
#print axioms HodgeBasketBRootMovingExtremalFinite.two_and_three_torsion_is_zero
#print axioms HodgeBasketBRootMovingExtremalFinite.nonzero_three_torsion_not_two_torsion
#print axioms HodgeBasketBRootMovingExtremalFinite.root_moving_forces_six
#print axioms HodgeBasketBRootMovingExtremalFinite.no_offroot_units_forces_all_five
#print axioms HodgeBasketBRootMovingExtremalFinite.root_moving_extremal

end HodgeBasketBRootMovingExtremalFinite
