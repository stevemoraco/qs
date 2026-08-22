import Mathlib

namespace FlagGaugeInvarianceCore

theorem invariant_on_transitive_action_is_constant
    {G X Y : Type*}
    [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (f : X → Y)
    (hinv : ∀ g : G, ∀ x : X, f (g • x) = f x) :
    ∀ x y : X, f x = f y := by
  intro x y
  rcases htrans x y with ⟨g, hg⟩
  calc
    f x = f (g • x) := (hinv g x).symm
    _ = f y := congrArg f hg

theorem nonconstant_on_transitive_action_not_invariant
    {G X Y : Type*}
    [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (f : X → Y)
    (hnonconstant : ∃ x y : X, f x ≠ f y) :
    ¬ (∀ g : G, ∀ x : X, f (g • x) = f x) := by
  intro hinv
  rcases hnonconstant with ⟨x, y, hxy⟩
  exact hxy (invariant_on_transitive_action_is_constant htrans f hinv x y)

theorem invariant_two_values_equal
    {G X Y : Type*}
    [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (f : X → Y)
    (hinv : ∀ g : G, ∀ x : X, f (g • x) = f x)
    (x y : X) :
    f x = f y :=
  invariant_on_transitive_action_is_constant htrans f hinv x y

#print axioms invariant_on_transitive_action_is_constant
#print axioms nonconstant_on_transitive_action_not_invariant
#print axioms invariant_two_values_equal

end FlagGaugeInvarianceCore
