import Mathlib

namespace NSBeltramiPolarization

/-- Abstract polarization firewall: if a quadratic map built from a biadditive
interaction vanishes on `x`, `y`, and `x+y`, then the symmetrized cross term
vanishes exactly. This is the algebra used for tangent Beltrami cancellation. -/
theorem cross_zero_of_diagonal_zero
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (B : V → V → W)
    (hleft : ∀ a b c, B (a + b) c = B a c + B b c)
    (hright : ∀ a b c, B a (b + c) = B a b + B a c)
    (x y : V)
    (hx : B x x = 0)
    (hy : B y y = 0)
    (hxy : B (x + y) (x + y) = 0) :
    B x y + B y x = 0 := by
  have h_expand :
      B (x + y) (x + y) =
        (B x x + B x y) + (B y x + B y y) := by
    rw [hleft, hright, hright]
  rw [h_expand, hx, hy] at hxy
  simpa [add_assoc, add_left_comm, add_comm] using hxy

/-- If the diagonal quadratic interaction vanishes on an additive subset closed
under addition, then every symmetrized tangent cross interaction vanishes. -/
theorem tangent_cross_zero
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (B : V → V → W)
    (S : Set V)
    (hadd : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
    (hdiag : ∀ x, x ∈ S → B x x = 0)
    (hleft : ∀ a b c, B (a + b) c = B a c + B b c)
    (hright : ∀ a b c, B a (b + c) = B a b + B a c)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    B x y + B y x = 0 := by
  apply cross_zero_of_diagonal_zero B hleft hright x y
  · exact hdiag x hx
  · exact hdiag y hy
  · exact hdiag (x + y) (hadd hx hy)

#print axioms cross_zero_of_diagonal_zero
#print axioms tangent_cross_zero

end NSBeltramiPolarization
