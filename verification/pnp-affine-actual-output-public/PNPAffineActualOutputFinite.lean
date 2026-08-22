import Mathlib

/-!
# P versus NP: actual affine-refuter output-family finite core

This file formalizes only the finite counting and arithmetic shadows from
`PNP_AFFINE_REFUTER_ACTUAL_OUTPUT_FAMILY_2026-08-12.md`.

It does not formalize Boolean circuits, Algorithm 2, affine refuters, sparse
languages, hardness magnification, NP, or P versus NP.
-/

namespace PNPAffineActualOutput

abbrev Assignment (k : ℕ) := Fin k → Bool
abbrev PairPoint (k : ℕ) := Sum (Fin k) (Fin k) → Bool

/-- Read the distinguished coordinate from each input pair. -/
def pairTag {k : ℕ} (x : PairPoint k) : Assignment k :=
  fun i => x (Sum.inl i)

/-- The coordinate coset indexed by `a`. -/
def pairFiber {k : ℕ} (a : Assignment k) : Set (PairPoint k) :=
  {x | pairTag x = a}

/-- A point belongs to at most one fiber. -/
theorem pairFiber_tag_unique {k : ℕ}
    {x : PairPoint k} {a b : Assignment k}
    (ha : x ∈ pairFiber a) (hb : x ∈ pairFiber b) : a = b := by
  exact ha.symm.trans hb

/-- Every assignment labels a nonempty coordinate coset. -/
theorem pairFiber_nonempty {k : ℕ} (a : Assignment k) :
    (pairFiber a).Nonempty := by
  let x : PairPoint k := fun s =>
    match s with
    | Sum.inl i => a i
    | Sum.inr _ => false
  refine ⟨x, ?_⟩
  funext i
  rfl

/-- There are exactly `2^k` assignment labels. -/
theorem assignment_card (k : ℕ) :
    Fintype.card (Assignment k) = 2 ^ k := by
  simp [Assignment]

/-- Any finite list of labels that covers every actual output tag has at least
    `2^k` entries.  This is the finite pigeonhole core of the blocker bound. -/
theorem surjective_labels_need_exp {k m : ℕ}
    (label : Fin m → Assignment k)
    (hlabel : Function.Surjective label) :
    2 ^ k ≤ m := by
  have hcard := Fintype.card_le_of_surjective label hlabel
  simpa [Assignment] using hcard

/-- The explicit source circuit has `3k-1` gates and reads `2k` inputs, so its
    source measure is `5k-1`. -/
theorem explicit_circuit_measure_ledger (k : ℕ) :
    (3 * k - 1) + 2 * k = 5 * k - 1 := by
  omega

/-- With `n=4m` and source parameter `d=m`, the explicit circuit size
    `6m-1` lies strictly below `3n-4d=8m`. -/
theorem source_size_budget (m : ℕ) (hm : 1 ≤ m) :
    6 * m - 1 < 8 * m := by
  omega

/-- Its exact source measure `10m-1` lies strictly below
    `4(n-d)=12m`. -/
theorem source_measure_budget (m : ℕ) (hm : 1 ≤ m) :
    10 * m - 1 < 12 * m := by
  omega

/-- The actual output dimension is `n/2=2m`, twice the guaranteed source
    parameter `d=m`. -/
theorem full_output_dimension (m : ℕ) :
    2 * m = (4 * m) / 2 := by
  omega

/-- The actual parallel output family has `2^(n/2)=2^(2m)` members. -/
theorem actual_output_family_count (m : ℕ) :
    Fintype.card (Assignment (2 * m)) = 2 ^ (2 * m) := by
  simpa using assignment_card (2 * m)

#print axioms pairFiber_tag_unique
#print axioms pairFiber_nonempty
#print axioms assignment_card
#print axioms surjective_labels_need_exp
#print axioms explicit_circuit_measure_ledger
#print axioms source_size_budget
#print axioms source_measure_budget
#print axioms full_output_dimension
#print axioms actual_output_family_count

end PNPAffineActualOutput
