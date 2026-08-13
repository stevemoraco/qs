import Mathlib

/-!
# Restriction-universal summary fibers

An embedding `embed : X → Z` with a left-inverse decoder `recover : Z → X`
is injective. If a summary is constant on the embedded image and base complexity
is bounded by lifted complexity, then arbitrary base hardness and semantic
variation live inside one exact summary fiber.
-/

namespace PvsNP.RestrictionUniversalFiber

variable {X Z Y : Type*}

/-- Data for a restriction-universal embedding into one summary fiber. -/
structure UniversalFiberData where
  embed : X → Z
  recover : Z → X
  summary : Z → Y
  summaryValue : Y
  recover_embed : Function.LeftInverse recover embed
  summary_embed : ∀ x : X, summary (embed x) = summaryValue

namespace UniversalFiberData

variable (D : UniversalFiberData (X := X) (Z := Z) (Y := Y))

/-- A restriction-universal embedding is automatically injective. -/
theorem embed_injective : Function.Injective D.embed :=
  D.recover_embed.injective

/-- Every embedded object lies in the designated exact summary fiber. -/
theorem embed_mem_fiber (x : X) :
    D.embed x ∈ {z : Z | D.summary z = D.summaryValue} := by
  exact D.summary_embed x

/-- Distinct base objects remain distinct inside the one summary fiber. -/
theorem distinct_embed {x₁ x₂ : X} (h : x₁ ≠ x₂) :
    D.embed x₁ ≠ D.embed x₂ := by
  exact fun hEq => h (D.embed_injective hEq)

/-- Recovering after embedding is exact. -/
theorem recover_exact (x : X) : D.recover (D.embed x) = x :=
  D.recover_embed x

/--
Any semantic label on the base class can vary inside the same exact summary
fiber whenever it varies on two base objects.
-/
theorem semantic_variation_in_one_fiber
    (label : X → Bool) {x₀ x₁ : X} (hLabel : label x₀ ≠ label x₁) :
    D.summary (D.embed x₀) = D.summary (D.embed x₁) ∧
      label (D.recover (D.embed x₀)) ≠ label (D.recover (D.embed x₁)) := by
  constructor
  · rw [D.summary_embed, D.summary_embed]
  · simpa [D.recover_embed x₀, D.recover_embed x₁] using hLabel

/-- Lift a base property to the embedded image. -/
def LiftProperty (Q : X → Prop) (z : Z) : Prop :=
  ∃ x : X, Q x ∧ D.embed x = z

/-- Every base member produces a member of the lifted property. -/
theorem mem_lift_of_mem (Q : X → Prop) {x : X} (hx : Q x) :
    D.LiftProperty Q (D.embed x) := by
  exact ⟨x, hx, rfl⟩

/-- Every lifted-property member lies in the designated summary fiber. -/
theorem lift_subset_fiber (Q : X → Prop) {z : Z}
    (hz : D.LiftProperty Q z) :
    D.summary z = D.summaryValue := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact D.summary_embed x

/-- On the embedded image, lifted-property membership is exactly base membership. -/
theorem lift_embed_iff (Q : X → Prop) (x : X) :
    D.LiftProperty Q (D.embed x) ↔ Q x := by
  constructor
  · rintro ⟨x', hx', hEq⟩
    have : x' = x := D.embed_injective hEq
    simpa [this] using hx'
  · exact D.mem_lift_of_mem Q

/--
If base cost transfers monotonically to the lifted object, every base lower
bound transfers to the lifted property.
-/
theorem lift_usefulness
    (costX : X → ℕ) (costZ : Z → ℕ)
    (hTransfer : ∀ x : X, costX x ≤ costZ (D.embed x))
    (Q : X → Prop) (B : ℕ)
    (hUseful : ∀ x : X, Q x → B < costX x) :
    ∀ z : Z, D.LiftProperty Q z → B < costZ z := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact lt_of_lt_of_le (hUseful x hx) (hTransfer x)

/--
An easy embedded representative blocks every strict lower-bound certificate that
depends only on the common summary value.
-/
theorem common_summary_easy_representative_obstruction
    (costZ : Z → ℕ) (B : ℕ) (xEasy : X)
    (hEasy : costZ (D.embed xEasy) ≤ B) :
    ¬ (∀ z : Z, D.summary z = D.summaryValue → B < costZ z) := by
  intro hCert
  exact (not_lt_of_ge hEasy) (hCert (D.embed xEasy) (D.summary_embed xEasy))

end UniversalFiberData

end PvsNP.RestrictionUniversalFiber
