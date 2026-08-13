import Mathlib

/-!
# P versus NP: pedigree-polytope specification audit cores

This file formalizes only finite logical countermodels extracted from the
source audit of `TiruArt/Pedigree-Polytopes-Lean4` at commit
`3c9c90ed2e38dd3a679891029c8e7622b5801988`.

It does **not** formalize P, NP, STSP, pedigree polytopes, multicommodity
flow, or the source repository.  Its purpose is to make three load-bearing
logical distinctions kernel-checkable:

1. a chain ending in an arbitrary proposition proves only what its hypotheses
   already contain;
2. a one-way sufficiency theorem is not a decision equivalence;
3. a strengthened feasibility certificate that contains a semantic witness
   does not follow from raw feasibility merely by naming the two notions alike.

The final scalar lemma records the incompatibility of two distinct unit masses
with one nonnegative unit budget.  This is the finite normalization warning
behind a certificate type which assigns value `1` to every commodity head.
-/

namespace PNPPedigreeSpecificationAudit

/-- An abstract implication chain is entirely parametric in its final goal.
No semantic content about the name of `Goal` is introduced by composition. -/
theorem abstract_chain_proves_only_assumed_goal
    {Quick Separation Optimisation STSP SAT Goal : Prop}
    (hQuick : Quick)
    (hSeparation : Quick → Separation)
    (hOptimisation : Separation → Optimisation)
    (hSTSP : Optimisation → STSP)
    (hKarp : STSP → SAT)
    (hCook : SAT → Goal) :
    Goal := by
  exact hCook (hKarp (hSTSP (hOptimisation (hSeparation hQuick))))

/-- A two-point model of membership.  Both points are members. -/
def Member (_x : Bool) : Prop := True

/-- A two-point model of a feasibility test.  Only `true` is feasible. -/
def Feasible (x : Bool) : Prop := x = true

/-- Feasibility is sufficient for membership in the countermodel. -/
theorem feasibility_is_sufficient :
    ∀ x : Bool, Feasible x → Member x := by
  intro _x _h
  trivial

/-- Membership is not necessary for feasibility in the same countermodel. -/
theorem membership_is_not_necessary :
    ¬ (∀ x : Bool, Member x → Feasible x) := by
  intro h
  have hfalse : Feasible false := h false trivial
  simp [Feasible] at hfalse

/-- Exact finite refutation of the silent upgrade
`feasible → member` to `feasible ↔ member`. -/
theorem one_direction_is_not_a_decider :
    (∀ x : Bool, Feasible x → Member x) ∧
    ¬ (∀ x : Bool, Member x → Feasible x) := by
  exact ⟨feasibility_is_sufficient, membership_is_not_necessary⟩

/-- A raw feasibility certificate with no semantic membership field. -/
structure RawFeasible where
  token : Unit

/-- A strengthened certificate carrying both raw feasibility and the desired
semantic witness.  The impossible witness makes the distinction visible. -/
structure StrengthenedFeasible where
  raw : RawFeasible
  semanticWitness : False

/-- Raw feasibility is inhabited. -/
theorem raw_feasibility_nonempty : Nonempty RawFeasible := by
  exact ⟨⟨()⟩⟩

/-- The strengthened certificate is empty because it contains the semantic
conclusion as a field. -/
theorem strengthened_feasibility_empty : IsEmpty StrengthenedFeasible := by
  exact ⟨fun h => h.semanticWitness.elim⟩

/-- Raw feasibility does not automatically construct the strengthened
certificate. -/
theorem raw_does_not_supply_baked_in_witness :
    Nonempty RawFeasible ∧ IsEmpty StrengthenedFeasible := by
  exact ⟨raw_feasibility_nonempty, strengthened_feasibility_empty⟩

/-- Any certificate containing a witness trivially yields that witness; this
is projection, not a theorem that raw feasibility implies the witness. -/
theorem baked_in_witness_projects
    {Raw Witness : Prop} (certificate : Raw ∧ Witness) : Witness := by
  exact certificate.2

/-- Two distinct coordinates normalized to one cannot fit inside a unit total
when all remaining mass is nonnegative. -/
theorem two_unit_coordinates_break_unit_budget
    {first second remainder : ℚ}
    (hfirst : first = 1)
    (hsecond : second = 1)
    (hremainder : 0 ≤ remainder)
    (htotal : first + second + remainder = 1) :
    False := by
  linarith

/-- Equal finite cardinality is compatible with opposite Boolean labels; a
cardinality inequality is not by itself a complexity-class semantics. -/
theorem opposite_labels_same_singleton_cardinality :
    ({true} : Finset Bool).card = 1 ∧
    ({false} : Finset Bool).card = 1 ∧
    true ≠ false := by
  simp

#print axioms abstract_chain_proves_only_assumed_goal
#print axioms feasibility_is_sufficient
#print axioms membership_is_not_necessary
#print axioms one_direction_is_not_a_decider
#print axioms raw_feasibility_nonempty
#print axioms strengthened_feasibility_empty
#print axioms raw_does_not_supply_baked_in_witness
#print axioms baked_in_witness_projects
#print axioms two_unit_coordinates_break_unit_budget
#print axioms opposite_labels_same_singleton_cardinality

end PNPPedigreeSpecificationAudit
