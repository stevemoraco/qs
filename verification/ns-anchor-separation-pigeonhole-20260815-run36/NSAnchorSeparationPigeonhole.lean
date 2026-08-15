import Mathlib

/-!
# Anchor-separation finite pigeonhole

Finite real inequalities only.  This file does **not** formalize cross products,
vorticity directions, Lei--Ren--Tian, Pineau--Vicol, Navier--Stokes, or a Clay
statement.

The intended geometric use is: once an external vector argument proves
`pairSeparation <= anchorLegA + anchorLegB`, a lower bound on `pairSeparation`
forces at least one anchor leg to pay half of that separation.
-/

namespace NSAnchorSeparationPigeonhole

/-- If a total separation `c` is covered by two nonnegative geometric legs,
one leg must pay at least half.  In fact no sign hypothesis is needed. -/
theorem one_leg_pays_half
    (c x y : ℝ)
    (hcover : c ≤ x + y) :
    c / 2 ≤ x ∨ c / 2 ≤ y := by
  by_contra h
  simp only [not_or, not_le] at h
  linarith

/-- Numerical specialization used with a same-time direction pair separated by
at least `1/2`: one anchor leg is separated by at least `1/4`. -/
theorem half_pair_forces_quarter_anchor
    (x y : ℝ)
    (hcover : (1 : ℝ) / 2 ≤ x + y) :
    (1 : ℝ) / 4 ≤ x ∨ (1 : ℝ) / 4 ≤ y := by
  simpa using one_leg_pays_half ((1 : ℝ) / 2) x y hcover

/-- If both anchor legs are strictly below a threshold, their sum is strictly
below twice that threshold.  This is the hostile contrapositive form. -/
theorem two_small_legs_cannot_cover
    (c x y : ℝ)
    (hx : x < c / 2)
    (hy : y < c / 2) :
    x + y < c := by
  linarith

#print axioms one_leg_pays_half
#print axioms half_pair_forces_quarter_anchor
#print axioms two_small_legs_cannot_cover

end NSAnchorSeparationPigeonhole
