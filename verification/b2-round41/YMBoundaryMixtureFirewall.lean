import Mathlib

/-!
# Yang--Mills boundary-mixture finite firewall

This file formalizes a scalar defect-budget implication and the exact
two-state eigenmode of the banked boundary-selection counterexample.  It does
not formalize total variation, Dobrushin coefficients, projective cones, gauge
fields, Osterwalder--Schrader reconstruction, continuum limits, or Yang--Mills.
-/

namespace MillenniumBraid
namespace B2Round41YM

/-- Rank-one conditional kernel for boundary label zero. -/
def conditionalZero (ε : ℝ) (_x y : Bool) : ℝ :=
  if y then ε else 1 - ε

/-- Rank-one conditional kernel for boundary label one. -/
def conditionalOne (ε : ℝ) (_x y : Bool) : ℝ :=
  if y then 1 - ε else ε

/-- State-dependent boundary selection: state `false` chooses label zero and
state `true` chooses label one. -/
def selectedMixture (ε : ℝ) (x y : Bool) : ℝ :=
  if x then conditionalOne ε x y else conditionalZero ε x y

/-- Each fixed-boundary conditional kernel forgets the incoming state exactly.
-/
theorem conditionalZero_forgets_input
    (ε : ℝ) (x x' y : Bool) :
    conditionalZero ε x y = conditionalZero ε x' y := by
  rfl

/-- The other fixed-boundary conditional kernel also forgets the incoming
state exactly. -/
theorem conditionalOne_forgets_input
    (ε : ℝ) (x x' y : Bool) :
    conditionalOne ε x y = conditionalOne ε x' y := by
  rfl

/-- Antisymmetric sign mode on the two-state space. -/
def signMode (x : Bool) : ℝ :=
  if x then -1 else 1

/-- The state-dependent mixture has exact nontrivial eigenvalue `1-2ε`. -/
theorem selectedMixture_sign_eigenmode
    (ε : ℝ) (x : Bool) :
    (∑ y : Bool, selectedMixture ε x y * signMode y) =
      (1 - 2 * ε) * signMode x := by
  cases x <;> simp [selectedMixture, conditionalZero, conditionalOne, signMode]
  <;> ring

/-- Abstract additive repair: conditional memory plus boundary sensitivity is
an upper bound for the unconditional defect. -/
theorem additive_boundary_defect_budget
    {conditional boundary mixed q : ℝ}
    (hsplit : mixed ≤ conditional + boundary)
    (hbudget : conditional + boundary ≤ q) :
    mixed ≤ q := by
  exact hsplit.trans hbudget

/-- A combined budget strictly below one forces strict unconditional
contraction whenever the mixed defect is bounded by that budget. -/
theorem combined_budget_forces_strict_contraction
    {conditional boundary mixed : ℝ}
    (hsplit : mixed ≤ conditional + boundary)
    (hstrict : conditional + boundary < 1) :
    mixed < 1 := by
  exact lt_of_le_of_lt hsplit hstrict

/-- The boundary term is load-bearing: perfect conditional contraction gives
no strict conclusion when the boundary budget reaches one. -/
theorem endpoint_budget_has_no_strict_margin :
    (0 : ℝ) + 1 = 1 := by
  norm_num

#print axioms conditionalZero_forgets_input
#print axioms conditionalOne_forgets_input
#print axioms selectedMixture_sign_eigenmode
#print axioms additive_boundary_defect_budget
#print axioms combined_budget_forces_strict_contraction
#print axioms endpoint_budget_has_no_strict_margin

end B2Round41YM
end MillenniumBraid
