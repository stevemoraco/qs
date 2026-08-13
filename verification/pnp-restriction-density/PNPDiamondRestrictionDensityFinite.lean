import Mathlib

namespace PNP.DiamondRestrictionDensity

def BoundaryBand (n r w : ℕ) : Prop :=
  w ≤ r ∨ n ≤ w + r

theorem projection_image_card_le_support
    {X Y : Type*} [DecidableEq Y]
    (support : Finset X) (projection : X → Y) :
    (support.image projection).card ≤ support.card := by
  exact Finset.card_image_le

theorem nonempty_assignment_count_le_support
    {X : Type*} (t : ℕ)
    (support : Finset X) (projection : X → (Fin t → Bool)) :
    (support.image projection).card ≤ support.card := by
  exact Finset.card_image_le

theorem constant_fraction_nonempty_forces_support
    {t q goodCount supportSize : ℕ}
    (hfrac : 2 ^ t ≤ q * goodCount)
    (hgood : goodCount ≤ supportSize) :
    2 ^ t ≤ q * supportSize := by
  exact hfrac.trans (Nat.mul_le_mul_left q hgood)

theorem uniform_assignment_density_impossible
    {X : Type*} (t q : ℕ)
    (support : Finset X) (projection : X → (Fin t → Bool))
    (hsparse : q * support.card < 2 ^ t) :
    ¬ (2 ^ t ≤ q * (support.image projection).card) := by
  intro hfrac
  have hcard : (support.image projection).card ≤ support.card := by
    exact Finset.card_image_le
  have hmul : q * (support.image projection).card ≤ q * support.card :=
    Nat.mul_le_mul_left q hcard
  have hcontra : 2 ^ t ≤ q * support.card := hfrac.trans hmul
  omega

theorem two_sided_boundary_pattern_fixes_few
    {n r a b k hi : ℕ}
    (hsplit : a + b + k = n)
    (hdeep : r + 1 < k)
    (hlow : BoundaryBand n r (a + 1))
    (hhiEq : hi + 1 = a + k)
    (hhigh : BoundaryBand n r hi) :
    a + b + 2 ≤ 2 * r := by
  unfold BoundaryBand at hlow hhigh
  rcases hlow with hlow | hlow
  · rcases hhigh with hhigh | hhigh <;> omega
  · omega

theorem deep_two_sided_pattern_impossible
    {n r a b k hi : ℕ}
    (hsplit : a + b + k = n)
    (hdeep : r + 1 < k)
    (hlow : BoundaryBand n r (a + 1))
    (hhiEq : hi + 1 = a + k)
    (hhigh : BoundaryBand n r hi)
    (htooDeep : 2 * r < a + b + 2) : False := by
  have hbound := two_sided_boundary_pattern_fixes_few
    hsplit hdeep hlow hhiEq hhigh
  omega

theorem radius_two_pattern_fixes_at_most_two
    {n a b k hi : ℕ}
    (hsplit : a + b + k = n)
    (hdeep : 3 < k)
    (hlow : BoundaryBand n 2 (a + 1))
    (hhiEq : hi + 1 = a + k)
    (hhigh : BoundaryBand n 2 hi) :
    a + b ≤ 2 := by
  have h := two_sided_boundary_pattern_fixes_few
    hsplit hdeep hlow hhiEq hhigh
  omega

#print axioms projection_image_card_le_support
#print axioms nonempty_assignment_count_le_support
#print axioms constant_fraction_nonempty_forces_support
#print axioms uniform_assignment_density_impossible
#print axioms two_sided_boundary_pattern_fixes_few
#print axioms deep_two_sided_pattern_impossible
#print axioms radius_two_pattern_fixes_at_most_two

end PNP.DiamondRestrictionDensity
