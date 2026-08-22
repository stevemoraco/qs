import Mathlib

namespace PNPLeeCollapseConverseFirewall

/-- A forward implication does not in general supply its converse.  This is the
minimal propositional countermodel behind the Total-Collapse audit. -/
theorem forward_does_not_imply_converse :
    let P : Prop := False
    let Q : Prop := True
    (P → Q) ∧ ¬ (Q → P) := by
  simp

/-- Specialized truth-value form: `False -> True` is valid while
`True -> False` is not. -/
theorem collapse_direction_countermodel :
    (False → True) ∧ ¬ (True → False) := by
  simp

#print axioms forward_does_not_imply_converse
#print axioms collapse_direction_countermodel

end PNPLeeCollapseConverseFirewall
