import Mathlib

namespace SixLaneAudit.UniformErrorBudgetSharpness

/-- The strict budget in the B5 half-gap firewall cannot be weakened to a
nonstrict `eps ≤ M/2` if the desired conclusion is the strict inequality
`M/2 < q`: the boundary case can attain equality exactly. -/
theorem nonstrict_budget_allows_boundary :
    ∃ (M eps q : ℝ),
      0 < M ∧
      eps ≤ M / 2 ∧
      |q - M| ≤ eps ∧
      ¬ (M / 2 < q) := by
  refine ⟨2, 1, 1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms nonstrict_budget_allows_boundary

end SixLaneAudit.UniformErrorBudgetSharpness
