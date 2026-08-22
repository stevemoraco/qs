import Mathlib

/-!
# Normal-form barriers for invariant lower-bound certificates

This file formalizes the abstract logical core of the normal-form barrier used in
`NORMAL_FORM_BARRIER.md`.

No algebraic structure on the relation is required: if a property is preserved
along a relation and every point has a related representative of cost at most
`B`, then every nonempty such property contains a point of cost at most `B`.
Consequently it cannot certify the strict pointwise lower bound `B < cost x`.
-/

namespace PvsNP.NormalFormBarrier

variable {X : Type*}

/-- `P` is invariant along `r`: related points either both satisfy `P` or both fail it. -/
def InvariantAlong (r : X → X → Prop) (P : X → Prop) : Prop :=
  ∀ ⦃x y : X⦄, r x y → (P x ↔ P y)

/--
If every point has a related representative of cost at most `B`, every point in
an invariant property has such a representative which remains in the property.
-/
theorem contains_low_cost_representative
    (r : X → X → Prop) (P : X → Prop) (cost : X → ℕ) (B : ℕ)
    (hInvariant : InvariantAlong r P)
    (hNormalForm : ∀ x : X, ∃ y : X, r x y ∧ cost y ≤ B)
    {x : X} (hx : P x) :
    ∃ y : X, P y ∧ cost y ≤ B := by
  obtain ⟨y, hxy, hyCost⟩ := hNormalForm x
  exact ⟨y, (hInvariant hxy).mp hx, hyCost⟩

/--
A nonempty invariant property cannot soundly certify a strict lower bound above
an orbit-wide normal-form upper bound.
-/
theorem invariant_certificate_obstruction
    (r : X → X → Prop) (P : X → Prop) (cost : X → ℕ) (B : ℕ)
    (hInvariant : InvariantAlong r P)
    (hNormalForm : ∀ x : X, ∃ y : X, r x y ∧ cost y ≤ B)
    (hNonempty : ∃ x : X, P x) :
    ¬ (∀ x : X, P x → B < cost x) := by
  rintro hLower
  obtain ⟨x, hx⟩ := hNonempty
  obtain ⟨y, hy, hyCost⟩ :=
    contains_low_cost_representative r P cost B hInvariant hNormalForm hx
  exact (not_lt_of_ge hyCost) (hLower y hy)

/--
Equivalent existential form: a nonempty invariant property contains a
counterexample to every proposed strict lower bound above `B`.
-/
theorem exists_counterexample_to_strict_lower_bound
    (r : X → X → Prop) (P : X → Prop) (cost : X → ℕ) (B : ℕ)
    (hInvariant : InvariantAlong r P)
    (hNormalForm : ∀ x : X, ∃ y : X, r x y ∧ cost y ≤ B)
    (hNonempty : ∃ x : X, P x) :
    ∃ y : X, P y ∧ ¬ B < cost y := by
  obtain ⟨x, hx⟩ := hNonempty
  obtain ⟨y, hy, hyCost⟩ :=
    contains_low_cost_representative r P cost B hInvariant hNormalForm hx
  exact ⟨y, hy, not_lt_of_ge hyCost⟩

end PvsNP.NormalFormBarrier
