import Mathlib

namespace NSDLSColorResonance

/-- Distinct disjoint symmetric colors cannot contain opposite elements. -/
theorem cross_color_not_opposite
    {V : Type*} [AddCommGroup V]
    (A B : Set V)
    (hdisj : Disjoint A B)
    (hsymA : ∀ x, x ∈ A → -x ∈ A)
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    y ≠ -x := by
  intro h
  subst h
  have hneg : -x ∈ A := hsymA x hx
  exact Set.disjoint_left.1 hdisj hneg hy

/-- Distinct disjoint colors cannot contain the same element. -/
theorem cross_color_not_equal
    {V : Type*}
    (A B : Set V)
    (hdisj : Disjoint A B)
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    y ≠ x := by
  intro h
  subst h
  exact Set.disjoint_left.1 hdisj hx hy

/-- Hence a cross-color sum cannot vanish. -/
theorem cross_color_sum_ne_zero
    {V : Type*} [AddCommGroup V]
    (A B : Set V)
    (hdisj : Disjoint A B)
    (hsymA : ∀ x, x ∈ A → -x ∈ A)
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    x + y ≠ 0 := by
  intro hzero
  have hyneg : y = -x := by
    exact eq_neg_of_add_eq_zero_left hzero
  exact cross_color_not_opposite A B hdisj hsymA hx hy hyneg

/-- Hence a cross-color difference cannot vanish. -/
theorem cross_color_sub_ne_zero
    {V : Type*} [AddCommGroup V]
    (A B : Set V)
    (hdisj : Disjoint A B)
    {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    x - y ≠ 0 := by
  intro hzero
  have hxy : x = y := sub_eq_zero.mp hzero
  exact (cross_color_not_equal A B hdisj hx hy) hxy.symm

#print axioms cross_color_not_opposite
#print axioms cross_color_not_equal
#print axioms cross_color_sum_ne_zero
#print axioms cross_color_sub_ne_zero

end NSDLSColorResonance
