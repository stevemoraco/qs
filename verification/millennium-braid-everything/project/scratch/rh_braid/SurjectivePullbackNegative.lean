import Mathlib

/-!
# Surjective pullback preserves existence of a negative direction

This is a tiny finite/formal bridge used in the RH interpolation lane.
It does NOT prove RH.  Its intended use is:

* `V` = the finite zero-evaluation map from the test-function coefficient space
  to the localized zero-coordinate space;
* `q` = the localized zero-side quadratic form;
* surjectivity of `V` = interpolation;
* a negative vector for `q` = an off-line hyperbolic direction.

Then a negative zero-side direction pulls back to an actual negative test vector.
-/

namespace RHProof
namespace SurjectivePullback

/--
PROVED (elementary): if `V : α → β` is surjective and `q` has a negative
value somewhere on `β`, then `q ∘ V` has a negative value on `α`.
-/
theorem exists_negative_pullback
    {α β : Type*}
    (V : α → β)
    (q : β → ℝ)
    (hV : Function.Surjective V)
    (hneg : ∃ y : β, q y < 0) :
    ∃ x : α, q (V x) < 0 := by
  rcases hneg with ⟨y, hy⟩
  rcases hV y with ⟨x, rfl⟩
  exact ⟨x, hy⟩

/--
Equivalent contradiction form: if every pullback value is nonnegative and `V`
is surjective, then `q` is nonnegative everywhere.
-/
theorem nonnegative_of_surjective_pullback_nonnegative
    {α β : Type*}
    (V : α → β)
    (q : β → ℝ)
    (hV : Function.Surjective V)
    (hpull : ∀ x : α, 0 ≤ q (V x)) :
    ∀ y : β, 0 ≤ q y := by
  intro y
  rcases hV y with ⟨x, rfl⟩
  exact hpull x

end SurjectivePullback
end RHProof
