import Mathlib

/-!
# A constant contradictory exact-3-CNF core

Four width-three clauses force a Boolean variable `z` to be true; another four
force it to be false. Erasing all literal signs preserves clause scopes and
produces an all-positive satisfiable core.
-/

namespace PvsNP.ExactThreeCNFCore

/-- Evaluation of a width-three disjunctive clause. -/
def clause3 (p q r : Bool) : Bool := p || q || r

/--
The conjunction of all four sign patterns on `a,b`, with `z` positive in each
clause. This formula forces `z = true`.
-/
def forceTrue (z a b : Bool) : Bool :=
  clause3 z a b &&
  clause3 z a (!b) &&
  clause3 z (!a) b &&
  clause3 z (!a) (!b)

/-- The analogous four clauses with `z` negated force `z = false`. -/
def forceFalse (z c d : Bool) : Bool :=
  forceTrue (!z) c d

/-- The eight-clause exact-3-CNF contradictory core. -/
def contradictoryCore (z a b c d : Bool) : Bool :=
  forceTrue z a b && forceFalse z c d

/-- Erasing every sign leaves two repeated all-positive clause scopes. -/
def signErasedCore (z a b c d : Bool) : Bool :=
  clause3 z a b && clause3 z a b &&
  clause3 z a b && clause3 z a b &&
  clause3 z c d && clause3 z c d &&
  clause3 z c d && clause3 z c d

/-- The first four clauses are true exactly when `z` is true. -/
theorem forceTrue_eq_true_iff (z a b : Bool) :
    forceTrue z a b = true ↔ z = true := by
  cases z <;> cases a <;> cases b <;> decide

/-- The second four clauses are true exactly when `z` is false. -/
theorem forceFalse_eq_true_iff (z c d : Bool) :
    forceFalse z c d = true ↔ z = false := by
  cases z <;> cases c <;> cases d <;> decide

/-- No assignment satisfies the eight-clause core. -/
theorem contradictoryCore_ne_true (z a b c d : Bool) :
    contradictoryCore z a b c d ≠ true := by
  cases z <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Equivalently, the core evaluates to false on every assignment. -/
theorem contradictoryCore_eq_false (z a b c d : Bool) :
    contradictoryCore z a b c d = false := by
  cases z <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The sign-erased core is satisfied by the all-true assignment. -/
theorem signErasedCore_allTrue :
    signErasedCore true true true true true = true := by
  decide

end PvsNP.ExactThreeCNFCore
