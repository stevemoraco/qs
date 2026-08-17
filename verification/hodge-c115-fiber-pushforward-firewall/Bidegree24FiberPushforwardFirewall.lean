import Mathlib

/-!
# Finite shadow of the Hodge C115 general-fibre pushforward firewall

For the C114 matrix family in the nef basis `(e,h)`, the first column is
exactly `h`. The geometric argument then studies the reduced degree-two
curve over a general elliptic fibre and decomposes its finite pushforward.

This file verifies only the integer and two-term arithmetic used by that
argument. It does not formalize K3 surfaces, finite-flat maps, cycle
pushforward, curve normalization, elliptic fibrations, or the Hodge
conjecture.
-/

namespace Millennium.Hodge.Bidegree24FiberPushforwardFirewall

/-- The C114 family `A_r=[[0,1],[1,4r+3]]` acting on column vectors. -/
def familyMap (r : ℤ) (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.2, v.1 + (4 * r + 3) * v.2)

/-- Fibre and nef-boundary basis vectors in `(e,h)` coordinates. -/
def fibreVector : ℤ × ℤ := (1, 0)
def hVector : ℤ × ℤ := (0, 1)

/-- Every member of the C114 family sends the elliptic-fibre class to `h`. -/
theorem family_sends_fibre_to_h (r : ℤ) :
    familyMap r fibreVector = hVector := by
  simp [familyMap, fibreVector, hVector]

/-- If two nonnegative integer contributions sum to one, exactly one is the
unit contribution. In the geometric application the contributions are
`d_i * (B_i · e)`. -/
theorem two_contributions_sum_one
    (x y : ℕ) (h : x + y = 1) :
    (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) := by
  omega

/-- In `(R,e)` coordinates, the possible horizontal residual class after a
vertical image of degree `d` is `R+(2-d)e`; its square is `2-2d`. -/
theorem residual_class_square (d : ℤ) :
    -2 + 2 * (2 - d) = 2 - 2 * d := by
  ring

/-- A curve meeting the elliptic fibre once can be a K3 section only if the
residual vertical degree is exactly two, because a section has square `-2`. -/
theorem section_square_forces_degree_two
    (d : ℤ) (hsection : 2 - 2 * d = -2) :
    d = 2 := by
  linarith

/-- The connected-case image class `h` has square `+2`, not the section
square `-2`. -/
theorem h_square_is_not_section_square :
    (2 : ℤ) ≠ -2 := by
  norm_num

/-- At the sole square-compatible split value `d=2`, the horizontal residual
coordinate is zero: `R+(2-d)e=R`. -/
theorem degree_two_residual_is_section_class :
    (2 : ℤ) - 2 = 0 := by
  norm_num

#print axioms family_sends_fibre_to_h
#print axioms two_contributions_sum_one
#print axioms residual_class_square
#print axioms section_square_forces_degree_two
#print axioms h_square_is_not_section_square
#print axioms degree_two_residual_is_section_class

end Millennium.Hodge.Bidegree24FiberPushforwardFirewall
