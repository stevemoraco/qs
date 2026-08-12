import Mathlib

namespace Run16FiniteCores
namespace PNPManyToOneSelector

theorem protected_subset_fixedPoints
    {α β : Type*}
    (P : Set β) (G : α → β) (D : β → α)
    (hselect : ∀ x ∈ P, G (D x) = x) :
    P ⊆ {x : β | G (D x) = x} := by
  intro x hx
  exact hselect x hx

theorem fixedPoints_subset_range
    {α β : Type*}
    (G : α → β) (D : β → α) :
    {x : β | G (D x) = x} ⊆ Set.range G := by
  intro x hx
  exact ⟨D x, hx⟩

theorem range_eq_fixedPoints
    {α β : Type*}
    (G : α → β) (D : β → α)
    (hselect : ∀ x ∈ Set.range G, G (D x) = x) :
    Set.range G = {x : β | G (D x) = x} := by
  apply Set.Subset.antisymm
  · exact protected_subset_fixedPoints (Set.range G) G D hselect
  · exact fixedPoints_subset_range G D

/-- Pure cancellation form of the near-`2n` selector budget. -/
theorem nearTwoN_selector_cost
    (sG sD n Δ : ℕ)
    (hcost : 2 * n + (Δ + 1) < 2 * n + (sG + sD)) :
    Δ + 1 < sG + sD := by
  exact Nat.lt_of_add_lt_add_left hcost

/-- Pure cancellation form of the near-`2n` retraction budget. -/
theorem nearTwoN_retraction_cost
    (sR n Δ : ℕ)
    (hcost : 2 * n + (Δ + 1) < 2 * n + sR) :
    Δ + 1 < sR := by
  exact Nat.lt_of_add_lt_add_left hcost

end PNPManyToOneSelector
end Run16FiniteCores
