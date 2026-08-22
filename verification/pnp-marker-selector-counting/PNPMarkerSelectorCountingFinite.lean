import Mathlib

/-!
# Constant-support marker selectors: finite counting core

HONESTY BOUNDARY:

This file formalizes only the cardinality of a Boolean toggle space and the
finite pigeonhole obstruction to a circuit-realization map being surjective.
It does not formalize Boolean circuits, selector blocks, NP, hardness
magnification, or P versus NP.
-/

namespace Millennium
namespace PNPMarkerSelectorCountingFinite

/-- Three nonreserved cross-edge orientations for every unordered pair of
    coordinate-pairs.  The second factor is deliberately represented by a
    finite index type of cardinality `choose m 2`; the geometric realization
    is outside this finite core. -/
abbrev ToggleIndex (m : ℕ) := Fin 3 × Fin (m.choose 2)

/-- A toggle table chooses independently whether each alternate marker block
    is present. -/
abbrev ToggleAssignment (m : ℕ) := ToggleIndex m → Bool

/-- The finite toggle index has the expected cardinality. -/
theorem toggleIndex_card (m : ℕ) :
    Fintype.card (ToggleIndex m) = 3 * m.choose 2 := by
  simp [ToggleIndex]

/-- The independent selector construction therefore has exactly
    `2^(3 * choose m 2)` toggle tables. -/
theorem toggleAssignment_card (m : ℕ) :
    Fintype.card (ToggleAssignment m) = 2 ^ (3 * m.choose 2) := by
  simp [ToggleAssignment, ToggleIndex, toggleIndex_card]

/-- A realization map from a strictly smaller finite circuit-description
    space cannot cover every selector table. -/
theorem too_few_circuits_not_surjective
    {Circuit Selector : Type*} [Fintype Circuit] [Fintype Selector]
    (realize : Circuit → Selector)
    (hcard : Fintype.card Circuit < Fintype.card Selector) :
    ¬ Function.Surjective realize := by
  intro hsurj
  have hle : Fintype.card Selector ≤ Fintype.card Circuit :=
    Fintype.card_le_of_surjective realize hsurj
  exact (Nat.not_le_of_lt hcard) hle

/-- Specialized finite counting gate for the marker toggle family. -/
theorem circuit_count_below_toggle_count_forces_missing_selector
    {Circuit : Type*} [Fintype Circuit]
    (m : ℕ) (realize : Circuit → ToggleAssignment m)
    (hcard : Fintype.card Circuit < 2 ^ (3 * m.choose 2)) :
    ¬ Function.Surjective realize := by
  apply too_few_circuits_not_surjective realize
  simpa [toggleAssignment_card] using hcard

/-- Equivalently, under the same strict cardinal inequality there exists a
    toggle table outside the realization range. -/
theorem exists_unrealized_toggle_assignment
    {Circuit : Type*} [Fintype Circuit]
    (m : ℕ) (realize : Circuit → ToggleAssignment m)
    (hcard : Fintype.card Circuit < 2 ^ (3 * m.choose 2)) :
    ∃ selector : ToggleAssignment m, selector ∉ Set.range realize := by
  have hnot : ¬ Function.Surjective realize :=
    circuit_count_below_toggle_count_forces_missing_selector
      m realize hcard
  by_contra hnone
  apply hnot
  intro selector
  have hrange : selector ∈ Set.range realize := by
    by_contra hmissing
    exact hnone ⟨selector, hmissing⟩
  simpa [Set.mem_range] using hrange

#print axioms Millennium.PNPMarkerSelectorCountingFinite.toggleIndex_card
#print axioms Millennium.PNPMarkerSelectorCountingFinite.toggleAssignment_card
#print axioms Millennium.PNPMarkerSelectorCountingFinite.too_few_circuits_not_surjective
#print axioms Millennium.PNPMarkerSelectorCountingFinite.circuit_count_below_toggle_count_forces_missing_selector
#print axioms Millennium.PNPMarkerSelectorCountingFinite.exists_unrealized_toggle_assignment

end PNPMarkerSelectorCountingFinite
end Millennium
