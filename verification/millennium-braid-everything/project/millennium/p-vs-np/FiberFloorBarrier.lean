import Mathlib

/-!
# Fiber-floor obstructions for coarse complexity summaries

If a lower-bound certificate depends only on a summary `σ x`, then every object
in the same summary fiber receives the same verdict. A single low-cost member of
a selected fiber therefore refutes any strict pointwise lower bound above that
cost.
-/

namespace PvsNP.FiberFloorBarrier

variable {X Y : Type*}

/-- A summary-level property intended to certify a strict complexity bound. -/
def SummaryCertificate
    (summary : X → Y) (cost : X → ℕ) (Q : Y → Prop) (B : ℕ) : Prop :=
  ∀ x : X, Q (summary x) → B < cost x

/-- A selected summary fiber has a representative of cost at most `B`. -/
def SelectedLowFiber
    (summary : X → Y) (cost : X → ℕ) (Q : Y → Prop) (B : ℕ) : Prop :=
  ∃ x : X, Q (summary x) ∧ cost x ≤ B

/-- One low-cost object in a selected fiber destroys a strict certificate. -/
theorem selected_low_fiber_obstruction
    (summary : X → Y) (cost : X → ℕ) (Q : Y → Prop) (B : ℕ)
    (hLow : SelectedLowFiber summary cost Q B) :
    ¬ SummaryCertificate summary cost Q B := by
  rintro hCert
  obtain ⟨x, hxQ, hxCost⟩ := hLow
  exact (not_lt_of_ge hxCost) (hCert x hxQ)

/--
Fiberwise formulation: if every selected realized summary has a low-cost
representative in the same fiber, then a nonempty selected region cannot certify
a strict bound.
-/
theorem fiber_floor_obstruction
    (summary : X → Y) (cost : X → ℕ) (Q : Y → Prop) (B : ℕ)
    (hSelected : ∃ x : X, Q (summary x))
    (hFiberLow : ∀ x : X, Q (summary x) →
      ∃ z : X, summary z = summary x ∧ cost z ≤ B) :
    ¬ SummaryCertificate summary cost Q B := by
  rintro hCert
  obtain ⟨x, hxQ⟩ := hSelected
  obtain ⟨z, hzx, hzCost⟩ := hFiberLow x hxQ
  have hzQ : Q (summary z) := by simpa [hzx] using hxQ
  exact (not_lt_of_ge hzCost) (hCert z hzQ)

/--
If two objects have the same summary but opposite semantic labels, no classifier
factoring through the summary can classify both correctly.
-/
theorem semantic_collision_obstruction
    (summary : X → Y) (label : X → Bool)
    {u v : X} (hSummary : summary u = summary v)
    (hLabel : label u ≠ label v) :
    ¬ ∃ classifier : Y → Bool,
      classifier (summary u) = label u ∧
      classifier (summary v) = label v := by
  rintro ⟨classifier, hu, hv⟩
  apply hLabel
  calc
    label u = classifier (summary u) := hu.symm
    _ = classifier (summary v) := by rw [hSummary]
    _ = label v := hv

/--
A summary-invariant property is just a union of summary fibers: equality of
summaries forces agreement of the property.
-/
theorem property_factors_through_summary_is_fiber_constant
    (summary : X → Y) (Q : Y → Prop)
    {u v : X} (hSummary : summary u = summary v) :
    Q (summary u) ↔ Q (summary v) := by
  rw [hSummary]

end PvsNP.FiberFloorBarrier
