import Mathlib

namespace Millennium.PNP.VegaForcedCutFalsifier

/-- A directed arc crosses when its tail is on the selected side and its
head is on the complementary side. -/
def crosses (tail head : Bool) : ℕ :=
  if tail = true ∧ head = false then 1 else 0

/-- The three forced arcs `(¬x,x)`, `(¬y,y)`, `(¬z,z)` used by the paper.
Feasibility orients every negated literal into the selected side and every
positive literal out of it; it does not leave one binary choice per variable. -/
def forcedFeasible
    (nx x ny y nz z : Bool) : Prop :=
  nx = true ∧ x = false ∧
  ny = true ∧ y = false ∧
  nz = true ∧ z = false

/-- The paper's three clause arcs `(¬x,y)`, `(¬y,z)`, `(¬z,x)`. -/
def clauseCost (nx x ny y nz z : Bool) : ℕ :=
  crosses nx y + crosses ny z + crosses nz x

/-- The three forced arcs themselves. -/
def forcedCost (nx x ny y nz z : Bool) : ℕ :=
  crosses nx x + crosses ny y + crosses nz z

/-- Total unit-weight cut cost for one three-variable clause. -/
def totalCost (nx x ny y nz z : Bool) : ℕ :=
  clauseCost nx x ny y nz z + forcedCost nx x ny y nz z

/-- A monotone three-variable clause is NAE-satisfied when it has at least
one true and at least one false variable. -/
def singleClauseNAE (x y z : Bool) : Prop :=
  (x = true ∨ y = true ∨ z = true) ∧
  (x = false ∨ y = false ∨ z = false)

/-- For `m=1,n=3`, the paper claims satisfiability iff its forced-cut graph
has a feasible cut of weight `m+n=4`. -/
def ClaimedSingleClauseEquivalence : Prop :=
  (∃ x y z : Bool, singleClauseNAE x y z) ↔
  (∃ nx x ny y nz z : Bool,
    forcedFeasible nx x ny y nz z ∧
    totalCost nx x ny y nz z = 4)

/-- BANKER: feasibility of the forced arcs pins all three clause arcs to
cross; the construction has no remaining assignment choice. -/
theorem banker_forced_edges_pin_every_clause_arc
    (nx x ny y nz z : Bool)
    (h : forcedFeasible nx x ny y nz z) :
    crosses nx y = 1 ∧ crosses ny z = 1 ∧ crosses nz x = 1 := by
  rcases h with ⟨hnx, hx, hny, hy, hnz, hz⟩
  simp [crosses, hnx, hx, hny, hy, hnz, hz]

/-- CRITIC: the one-clause NAE instance is satisfiable, while every feasible
cut in the paper's graph has clause cost `3` and total cost `6`, not `4`. -/
theorem critic_satisfiable_clause_but_every_feasible_cut_costs_six :
    (∃ x y z : Bool, singleClauseNAE x y z) ∧
    (∀ nx x ny y nz z : Bool,
      forcedFeasible nx x ny y nz z →
      clauseCost nx x ny y nz z = 3 ∧
      totalCost nx x ny y nz z = 6) := by
  constructor
  · exact ⟨true, false, false, by simp [singleClauseNAE]⟩
  · intro nx x ny y nz z h
    rcases h with ⟨hnx, hx, hny, hy, hnz, hz⟩
    simp [clauseCost, totalCost, forcedCost, crosses,
      hnx, hx, hny, hy, hnz, hz]

/-- CLEANER: the claimed weight-`m+n` equivalence already fails for one
satisfiable monotone NAE clause on three variables. -/
theorem cleaner_claimed_single_clause_equivalence_is_false :
    ¬ ClaimedSingleClauseEquivalence := by
  intro h
  have hsat : ∃ x y z : Bool, singleClauseNAE x y z :=
    ⟨true, false, false, by simp [singleClauseNAE]⟩
  obtain ⟨nx, x, ny, y, nz, z, hfeasible, hfour⟩ := h.mp hsat
  have hsix : totalCost nx x ny y nz z = 6 :=
    (critic_satisfiable_clause_but_every_feasible_cut_costs_six.2
      nx x ny y nz z hfeasible).2
  omega

#print axioms banker_forced_edges_pin_every_clause_arc
#print axioms critic_satisfiable_clause_but_every_feasible_cut_costs_six
#print axioms cleaner_claimed_single_clause_equivalence_is_false

end Millennium.PNP.VegaForcedCutFalsifier
