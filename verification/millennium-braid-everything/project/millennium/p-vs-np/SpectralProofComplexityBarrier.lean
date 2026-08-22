import Mathlib

/-!
# Sign erasure and identical CNF incidence scopes

This file formalizes the finite incidence-identity core of
`SPECTRAL_PROOF_COMPLEXITY_BARRIER.md`.
-/

namespace PvsNP.SpectralProofComplexityBarrier

variable {Var : Type*}

/-- A Boolean literal consists of a variable and a negation bit. -/
structure Lit (Var : Type*) where
  var : Var
  neg : Bool
  deriving DecidableEq, Repr

abbrev Clause (Var : Type*) := List (Lit Var)
abbrev CNF (Var : Type*) := List (Clause Var)

/-- Erase literal signs while retaining every variable occurrence and clause slot. -/
def eraseSigns (F : CNF Var) : List (List Var) :=
  F.map (List.map Lit.var)

/-- Replace every literal by the positive occurrence of the same variable. -/
def allPositive (F : CNF Var) : CNF Var :=
  F.map fun C => C.map fun ℓ => ⟨ℓ.var, false⟩

/-- Making every occurrence positive leaves the complete incidence data unchanged. -/
theorem eraseSigns_allPositive (F : CNF Var) :
    eraseSigns (allPositive F) = eraseSigns F := by
  simp [eraseSigns, allPositive]

/-- Positive unit literal. -/
def pos (v : Var) : Lit Var := ⟨v, false⟩

/-- Negative unit literal. -/
def neg (v : Var) : Lit Var := ⟨v, true⟩

/-- Two same-sign fresh unit clauses used on the hard side. -/
def hardPadding (z : Var) : CNF Var := [[[pos z]], [[pos z]]]

/-- A contradictory fresh unit pair used on the easy side. -/
def easyPadding (z : Var) : CNF Var := [[[pos z]], [[neg z]]]

/-- The two paddings have exactly the same unsigned incidence scopes. -/
theorem eraseSigns_padding_eq (z : Var) :
    eraseSigns (hardPadding z) = eraseSigns (easyPadding z) := by
  rfl

/-- Hard-side formula: retain `H` and add two positive fresh units. -/
def hardFormula (H : CNF Var) (z : Var) : CNF Var :=
  H ++ hardPadding z

/-- Easy-side formula: make the old scopes jointly satisfiable, then add a contradiction. -/
def easyFormula (H : CNF Var) (z : Var) : CNF Var :=
  allPositive H ++ easyPadding z

/-- The hard and easy formulas have identical complete unsigned incidence data. -/
theorem eraseSigns_hard_eq_easy (H : CNF Var) (z : Var) :
    eraseSigns (hardFormula H z) = eraseSigns (easyFormula H z) := by
  simp [hardFormula, easyFormula, eraseSigns, eraseSigns_allPositive,
    eraseSigns_padding_eq]

end PvsNP.SpectralProofComplexityBarrier
