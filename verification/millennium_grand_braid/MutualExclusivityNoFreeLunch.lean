import Millennium.GrandBraid.UnifiedSevenProblemBraid

/-!
# Mutual exclusivity does not supply coverage

This companion file addresses the tempting but invalid inference that a family of
mutually exclusive proof routes must contain a true route.  Exclusivity says that
at most one route can hold; it does not prove that at least one route holds.

The result is purely logical and is intentionally separate from every open Clay
statement.  A genuine inversion becomes decisive only after native mathematics
supplies a sound certificate on one side.
-/

namespace MillenniumGrandBraid

/-- Pairwise exclusivity of two propositions does not imply that either one is
true.  `False, False` is the smallest exact countermodel. -/
theorem mutualExclusivityDoesNotSupplyCoverage :
    ¬ (∀ P Q : Prop, (P → ¬ Q) → (Q → ¬ P) → (P ∨ Q)) := by
  intro h
  have hff : False ∨ False :=
    h False False (fun hf => False.elim hf) (fun hf => False.elim hf)
  cases hff with
  | inl hf => exact hf
  | inr hf => exact hf

/-- Even classical excluded middle `P ∨ ¬P` adds no proof power toward `P`:
the implication from excluded middle to `P` is equivalent to already having
`P`.  This is the exact firewall against treating a dichotomy as a solution. -/
theorem excludedMiddleToTargetIffTarget (P : Prop) :
    ((P ∨ ¬ P) → P) ↔ P := by
  constructor
  · intro h
    exact h (Classical.em P)
  · intro hP _
    exact hP

/-- A sound inversion audit plus a concrete positive certificate resolves the
positive side; without the certificate the audit proves only non-coexistence. -/
theorem inversionNeedsWitnessPositive
    {α : Type} {P : Prop} (A : InversionAudit α P) :
    (∃ x : α, A.cert x) → P := by
  rintro ⟨x, hx⟩
  exact A.positiveSound x hx

/-- Likewise, a concrete inverted certificate resolves the negative side. -/
theorem inversionNeedsWitnessNegative
    {α : Type} {P : Prop} (A : InversionAudit α P) :
    (∃ x : α, A.cert (A.I.inv x)) → ¬ P := by
  rintro ⟨x, hx⟩
  exact A.invertedSound x hx

#print axioms mutualExclusivityDoesNotSupplyCoverage
#print axioms excludedMiddleToTargetIffTarget
#print axioms inversionNeedsWitnessPositive
#print axioms inversionNeedsWitnessNegative

end MillenniumGrandBraid
