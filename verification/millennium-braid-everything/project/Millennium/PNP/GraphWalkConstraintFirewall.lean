import Mathlib

/-!
# P versus NP: constrained graph-walk firewall

A polynomial-size layered graph may have exponentially many choice walks.
Moreover, the fact that every local coordinate value extends to some globally
valid walk does not imply that an arbitrary combination of locally allowed
values is globally valid.

This is the finite combinatorial core needed to audit algorithms that call a
routine such as `TakeArbitraryComputationWalk` while charging only the length of
the returned walk.  If walk validity contains nonlocal consistency constraints,
finding such a walk is not justified by ordinary graph reachability or by the
output-length bound alone.

This file does not define Turing machines, SAT, NP, polynomial time, the paper's
footmark graph, or `P = NP` / `P ≠ NP`.
-/

namespace Millennium.PNP.GraphWalkConstraint

/-- A length-`n` binary choice walk through a two-choice layered graph. -/
abbrev ChoiceWalk (n : ℕ) := Fin n → Bool

/-- A concrete layered-node type: `n+1` layers and two vertices per layer. -/
abbrev LayerNode (n : ℕ) := Fin (n + 1) × Bool

/-- The layered graph has only linearly many vertices. -/
theorem layerNode_card (n : ℕ) :
    Fintype.card (LayerNode n) = (n + 1) * 2 := by
  simp [LayerNode]

/-- Nevertheless its binary layer choices form an exponential family. -/
theorem choiceWalk_card (n : ℕ) :
    Fintype.card (ChoiceWalk n) = 2 ^ n := by
  simp [ChoiceWalk]

/-- The exact finite size ledger: linear node count, exponential walk count. -/
theorem linear_nodes_exponential_walks (n : ℕ) :
    Fintype.card (LayerNode n) = (n + 1) * 2 ∧
    Fintype.card (ChoiceWalk n) = 2 ^ n := by
  exact ⟨layerNode_card n, choiceWalk_card n⟩

/-- A globally correlated two-layer validity predicate. -/
def correlated2 (w : ChoiceWalk 2) : Prop := w 0 = w 1

/-- Every value at every individual layer extends to some globally correlated
walk.  This is the strongest possible one-coordinate local extendability. -/
theorem every_local_value_extends (i : Fin 2) (b : Bool) :
    ∃ w : ChoiceWalk 2, correlated2 w ∧ w i = b := by
  refine ⟨fun _ => b, ?_, rfl⟩
  rfl

/-- A mixed walk made from individually allowed values. -/
def mixed2 : ChoiceWalk 2 := fun i => if i = 0 then false else true

/-- The mixed walk violates the global correlation constraint. -/
theorem mixed2_not_correlated : ¬ correlated2 mixed2 := by
  simp [correlated2, mixed2]

/-- Every coordinate of the mixed walk is locally extendable, yet the mixed
combination is not globally valid. -/
theorem all_local_extensions_do_not_force_global :
    (∀ i : Fin 2,
      ∃ w : ChoiceWalk 2, correlated2 w ∧ w i = mixed2 i) ∧
    ¬ correlated2 mixed2 := by
  constructor
  · intro i
    exact every_local_value_extends i (mixed2 i)
  · exact mixed2_not_correlated

/-- For an arbitrary global predicate on choice walks, constrained-walk
existence is exactly the original existential search over all assignments.
This tautological interface is deliberately explicit: a graph wrapper does not
remove the global predicate. -/
theorem constrained_walk_exists_exact
    {n : ℕ} (P : ChoiceWalk n → Prop) :
    (∃ w : ChoiceWalk n, P w) ↔ ∃ a : Fin n → Bool, P a := by
  rfl

/-- A selector satisfying a global predicate is already a witness for the
underlying assignment predicate; no extra algorithmic content is gained by
renaming it a walk selector. -/
theorem constrained_selector_returns_assignment
    {n : ℕ} {P : ChoiceWalk n → Prop}
    (select : ChoiceWalk n) (hselect : P select) :
    ∃ a : Fin n → Bool, P a := by
  exact ⟨select, hselect⟩

#print axioms layerNode_card
#print axioms choiceWalk_card
#print axioms linear_nodes_exponential_walks
#print axioms every_local_value_extends
#print axioms mixed2_not_correlated
#print axioms all_local_extensions_do_not_force_global
#print axioms constrained_walk_exists_exact
#print axioms constrained_selector_returns_assignment

end Millennium.PNP.GraphWalkConstraint
