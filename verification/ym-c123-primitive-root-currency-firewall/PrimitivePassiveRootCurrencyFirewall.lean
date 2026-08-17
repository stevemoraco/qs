import Mathlib

/-!
# Yang--Mills primitive passive-root currency firewall

Finite data and arithmetic only.

A norm may declare that an activity carries at most two passive exterior roots
while its displayed formula controls only bulk/structural/source coordinates.
Root-preserving maps and a finite root-placement theorem cannot manufacture a
uniform estimate for the omitted primitive root amplitude.

The countermodel below has:

* exactly two admitted passive roots;
* zero printed bulk/source row at every cutoff;
* an identity propagation map, hence perfect preservation and operator norm one
  in the printed currency;
* fixed one-vertex placement cost; and
* primitive root amplitude `cutoff + 1`.

Thus every listed preservation statement can hold while the primitive root row
is unbounded. A direct root seminorm and a uniform root-atom estimate are
logically necessary.

This file does **not** formalize Kirk's manuscript, replica--BKAR, Banach
activities, renormalization, lattice gauge theory, Osterwalder--Schrader
reconstruction, Yang--Mills, or any Clay theorem.
-/

namespace Millennium.YangMills.PrimitivePassiveRootCurrencyFirewall

/-- Finite shadow of a marked activity. `bulk` is everything visible to the
printed structural/source norm; `rootAmp` is the omitted primitive exterior-root
amplitude; `rootCount` records the declared number of roots. -/
structure MarkedActivity where
  bulk : ℕ
  rootAmp : ℕ
  rootCount : ℕ
  deriving DecidableEq

/-- The displayed currency sees only the bulk/source component. -/
def printedNorm (x : MarkedActivity) : ℕ := x.bulk

/-- The genuinely needed primitive-root currency. -/
def rootNorm (x : MarkedActivity) : ℕ := x.rootAmp

/-- Every fixed passive-source order has the same zero row in this countermodel. -/
def sourceRow (_order : ℕ) (x : MarkedActivity) : ℕ := x.bulk

/-- Propagation can preserve the marked activity perfectly. -/
def propagate (x : MarkedActivity) : MarkedActivity := x

/-- A hostile cutoff family: two declared roots, zero printed row, and growing
primitive root amplitude. -/
def hostile (cutoff : ℕ) : MarkedActivity where
  bulk := 0
  rootAmp := cutoff + 1
  rootCount := 2

/-- The hostile family satisfies the declared `at most two roots` inventory. -/
@[simp] theorem hostile_has_at_most_two_roots (cutoff : ℕ) :
    (hostile cutoff).rootCount ≤ 2 := by
  simp [hostile]

/-- Every displayed structural/source row can vanish uniformly. -/
@[simp] theorem hostile_printed_row_zero (cutoff : ℕ) :
    printedNorm (hostile cutoff) = 0 := by
  rfl

/-- Arbitrary fixed passive-source order adds no information about the omitted
root component in this model. -/
@[simp] theorem hostile_source_row_zero (order cutoff : ℕ) :
    sourceRow order (hostile cutoff) = 0 := by
  rfl

/-- Identity propagation has exact operator norm one in the printed currency. -/
theorem propagation_is_printed_norm_isometry (x : MarkedActivity) :
    printedNorm (propagate x) = printedNorm x := by
  rfl

/-- Identity propagation also preserves both the root inventory and its full
amplitude exactly. -/
theorem propagation_preserves_root_data (x : MarkedActivity) :
    (propagate x).rootCount = x.rootCount ∧
      rootNorm (propagate x) = rootNorm x := by
  exact ⟨rfl, rfl⟩

/-- The primitive root row exceeds every proposed cutoff-independent bound. -/
theorem primitive_root_exceeds_every_bound (C : ℕ) :
    ∃ cutoff : ℕ, C < rootNorm (hostile cutoff) := by
  refine ⟨C, ?_⟩
  simp [rootNorm, hostile]

/-- Consequently no cutoff-independent primitive-root bound exists. -/
theorem no_uniform_primitive_root_bound :
    ¬ ∃ C : ℕ, ∀ cutoff : ℕ, rootNorm (hostile cutoff) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨cutoff, hcutoff⟩ := primitive_root_exceeds_every_bound C
  exact (not_lt_of_ge (hC cutoff)) hcutoff

/-- Even allowing a fixed affine prefactor times the displayed norm cannot
control the omitted root component. -/
theorem no_fixed_handoff_from_printed_to_root_currency :
    ¬ ∃ C : ℕ, ∀ cutoff : ℕ,
      rootNorm (hostile cutoff) ≤ C * (printedNorm (hostile cutoff) + 1) := by
  rintro ⟨C, hC⟩
  have h := hC C
  simp [rootNorm, printedNorm, hostile] at h

/-- A one-vertex tree has fixed two-root placement cost, so the countermodel is
not caused by growing tree or placement entropy. -/
def twoRootPlacementCost (vertices : ℕ) : ℕ := vertices ^ 2

@[simp] theorem one_vertex_two_root_placement_cost :
    twoRootPlacementCost 1 = 1 := by
  simp [twoRootPlacementCost]

/-- Paying the complete fixed placement cost still does not bound the primitive
root atom uniformly. -/
theorem fixed_placement_does_not_bound_primitive_root (C : ℕ) :
    ∃ cutoff : ℕ,
      C * twoRootPlacementCost 1 < rootNorm (hostile cutoff) := by
  refine ⟨C, ?_⟩
  simp [twoRootPlacementCost, rootNorm, hostile]

/-- Complete no-free-lunch package: declared roots, all-order zero source rows,
perfect root-preserving propagation, and fixed placement cost coexist with an
unbounded primitive root row. -/
theorem declaration_and_preservation_do_not_create_a_root_atom_bound :
    (∀ cutoff : ℕ, (hostile cutoff).rootCount ≤ 2) ∧
    (∀ order cutoff : ℕ, sourceRow order (hostile cutoff) = 0) ∧
    (∀ x : MarkedActivity, printedNorm (propagate x) = printedNorm x) ∧
    (∀ x : MarkedActivity,
      (propagate x).rootCount = x.rootCount ∧
        rootNorm (propagate x) = rootNorm x) ∧
    (∀ C : ℕ, ∃ cutoff : ℕ,
      C * twoRootPlacementCost 1 < rootNorm (hostile cutoff)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hostile_has_at_most_two_roots
  · exact hostile_source_row_zero
  · exact propagation_is_printed_norm_isometry
  · exact propagation_preserves_root_data
  · exact fixed_placement_does_not_bound_primitive_root

/-- Once a genuine primitive root row is supplied, a root-preserving map
transfers it. This is the valid direction of implication. -/
theorem genuine_root_bound_transfers_through_preservation
    {X : Type*}
    (rootSize : X → ℕ)
    (step : X → X)
    (C : ℕ)
    (hBound : ∀ x : X, rootSize x ≤ C)
    (hPreserve : ∀ x : X, rootSize (step x) = rootSize x) :
    ∀ x : X, rootSize (step x) ≤ C := by
  intro x
  rw [hPreserve x]
  exact hBound x

#print axioms hostile_has_at_most_two_roots
#print axioms hostile_printed_row_zero
#print axioms hostile_source_row_zero
#print axioms propagation_is_printed_norm_isometry
#print axioms propagation_preserves_root_data
#print axioms primitive_root_exceeds_every_bound
#print axioms no_uniform_primitive_root_bound
#print axioms no_fixed_handoff_from_printed_to_root_currency
#print axioms one_vertex_two_root_placement_cost
#print axioms fixed_placement_does_not_bound_primitive_root
#print axioms declaration_and_preservation_do_not_create_a_root_atom_bound
#print axioms genuine_root_bound_transfers_through_preservation

end Millennium.YangMills.PrimitivePassiveRootCurrencyFirewall
