import Mathlib

namespace PNPEqualityRankFirewallFinite

/-- The exact logical content of a lower bound on pathology-free objects:
`¬ pathology → B ≤ g` only gives pathology for the strict range `g < B`. -/
theorem strict_budget_forces_pathology
    (g B : ℕ) (pathology : Prop)
    (hLower : ¬ pathology → B ≤ g)
    (hStrict : g < B) :
    pathology := by
  by_contra hNoPathology
  exact (Nat.not_lt_of_ge (hLower hNoPathology)) hStrict

/-- At an inclusive budget `g ≤ B`, the same hypothesis leaves one residue:
if no pathology occurs, then the size must be exactly the boundary `B`. -/
theorem inclusive_budget_residue_is_equality
    (g B : ℕ) (pathology : Prop)
    (hLower : ¬ pathology → B ≤ g)
    (hBudget : g ≤ B)
    (hNoPathology : ¬ pathology) :
    g = B := by
  exact Nat.le_antisymm hBudget (hLower hNoPathology)

/-- Truth-table representation of a unary Boolean map.  The first coordinate
is the value at `false`, the second the value at `true`. -/
abbrev Unary := Bool × Bool

/-- Evaluate a unary Boolean truth table. -/
def evalUnary (f : Unary) (x : Bool) : Bool :=
  if x then f.2 else f.1

/-- Composition of unary Boolean truth tables, with `g` applied first. -/
def compUnary (f g : Unary) : Unary :=
  (evalUnary f (evalUnary g false), evalUnary f (evalUnary g true))

/-- A unary Boolean map has rank two exactly when its two truth-table entries
differ.  We call this `NonConst`; the other two unary maps are constants. -/
def NonConst (f : Unary) : Prop :=
  f.1 ≠ f.2

/-- On a two-point set, composition is nonconstant iff both factors are
nonconstant.  This is the finite rank-multiplicativity invariant used by the
serial critical-path firewall. -/
@[simp] theorem nonConst_comp_iff (f g : Unary) :
    NonConst (compUnary f g) ↔ NonConst f ∧ NonConst g := by
  rcases f with ⟨f0, f1⟩
  rcases g with ⟨g0, g1⟩
  cases f0 <;> cases f1 <;> cases g0 <;> cases g1 <;> decide

/-- Five unary factors in chronological order:
`c0`, first occurrence of the live variable, `c1`, second occurrence, `c2`.
The context factors are independent of the live variable; the `t` factors
are the fixed branch maps induced by the two circuit gates reading it. -/
def chain5 (c0 t1 c1 t2 c2 : Unary) : Unary :=
  compUnary c2 (compUnary t2 (compUnary c1 (compUnary t1 c0)))

/-- Two-occurrence unary-rank coupling.

If, under one background, both values of the live variable leave a
nonconstant map from an earlier one-bit state to the output, then all four
fixed branch maps at its two occurrences are nonconstant.  Under every other
background (which changes only the branch-independent contexts), the two
branches therefore have the same constant/nonconstant status.

This is exactly the finite core needed to rule out an XOR low face together
with an AND high face in a one-bit serial `B₂` spine. -/
theorem twoOccurrence_rank_coupling
    (t10 t11 t20 t21 : Unary)
    (low0 low1 low2 high0 high1 high2 : Unary)
    (hLowBranch0 : NonConst (chain5 low0 t10 low1 t20 low2))
    (hLowBranch1 : NonConst (chain5 low0 t11 low1 t21 low2)) :
    NonConst (chain5 high0 t10 high1 t20 high2) ↔
      NonConst (chain5 high0 t11 high1 t21 high2) := by
  simp only [chain5, nonConst_comp_iff] at hLowBranch0 hLowBranch1 ⊢
  tauto

/-- The rank-coupling theorem forbids the mixed high-branch profile required
by an AND face once the low face has the two nonconstant branches required by
XOR. -/
theorem no_mixed_high_rank_after_two_nonconstant_low_branches
    (t10 t11 t20 t21 : Unary)
    (low0 low1 low2 high0 high1 high2 : Unary)
    (hLowBranch0 : NonConst (chain5 low0 t10 low1 t20 low2))
    (hLowBranch1 : NonConst (chain5 low0 t11 low1 t21 low2)) :
    ¬ ((NonConst (chain5 high0 t10 high1 t20 high2) ∧
          ¬ NonConst (chain5 high0 t11 high1 t21 high2)) ∨
        (¬ NonConst (chain5 high0 t10 high1 t20 high2) ∧
          NonConst (chain5 high0 t11 high1 t21 high2))) := by
  have hCoupled := twoOccurrence_rank_coupling
    t10 t11 t20 t21 low0 low1 low2 high0 high1 high2
    hLowBranch0 hLowBranch1
  tauto

#print axioms strict_budget_forces_pathology
#print axioms inclusive_budget_residue_is_equality
#print axioms nonConst_comp_iff
#print axioms twoOccurrence_rank_coupling
#print axioms no_mixed_high_rank_after_two_nonconstant_low_branches

end PNPEqualityRankFirewallFinite
