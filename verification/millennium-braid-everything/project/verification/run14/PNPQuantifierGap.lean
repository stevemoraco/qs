import Mathlib

namespace MillenniumRun14

/-- A finite countermodel to swapping `forall exists` into `exists forall`. -/
theorem pnp_quantifier_swap_counterexample :
    (∀ k : Bool, ∃ l : Bool, l = k) ∧
      ¬ (∃ l : Bool, ∀ k : Bool, l = k) := by
  decide

end MillenniumRun14
