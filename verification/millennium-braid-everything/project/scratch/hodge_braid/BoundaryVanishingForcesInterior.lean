import Mathlib

/-!
# Finite exactness core for the Hodge boundary/interior audit

This isolates the elementary logical step used in the Baily--Borel audit:
if the next boundary cohomology group vanishes, exactness forces the
compact-support/relative-to-absolute map to be surjective.

No geometry is encoded here; this is only the finite formal core.
-/

namespace HodgeBraid

/--
Abstract exact-sequence lemma.  Think of

  `f : H_c^n(X) → H^n(X)`
  `g : H^n(X) → H^n(B)`.

If exactness at `H^n(X)` is supplied in elementwise form and the boundary
codomain is a subsingleton (the zero group), then every absolute class is
in the image of compact support.
-/
theorem surjective_of_exact_and_next_zero
    {A B C : Type*} [Zero C] [Subsingleton C]
    (f : A → B) (g : B → C)
    (hexact : ∀ b : B, g b = 0 → ∃ a : A, f a = b) :
    Function.Surjective f := by
  intro b
  apply hexact b
  exact Subsingleton.elim _ _

/--
A contradiction form tailored to a claimed non-interior class: under the
same hypotheses, there cannot exist `b : B` outside the image of `f`.
-/
theorem no_nonimage_class_of_exact_and_next_zero
    {A B C : Type*} [Zero C] [Subsingleton C]
    (f : A → B) (g : B → C)
    (hexact : ∀ b : B, g b = 0 → ∃ a : A, f a = b) :
    ¬ ∃ b : B, ∀ a : A, f a ≠ b := by
  intro h
  rcases h with ⟨b, hb⟩
  rcases surjective_of_exact_and_next_zero f g hexact b with ⟨a, ha⟩
  exact hb a ha

end HodgeBraid
