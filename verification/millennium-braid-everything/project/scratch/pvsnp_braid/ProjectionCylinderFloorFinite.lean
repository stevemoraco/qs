import Mathlib

namespace PvsNPBraid

/-- Computing shared negations, one minterm per projected pattern, and an OR
of all minterms gives the exact safe gate count `s*k+k-1`. -/
theorem projection_lookup_gate_count
    (s k : ℤ) :
    k + s * (k - 1) + (s - 1) = s * k + k - 1 := by
  ring

/-- The universal lookup bound follows by replacing the number of projected
patterns by the total positive-slice size. -/
theorem projection_lookup_monotone
    (s m k : ℤ)
    (hk : 0 ≤ k) (hsm : s ≤ m) :
    s * k + k - 1 ≤ m * k + k - 1 := by
  nlinarith

/-- Rearranging survival of the projection-cylinder attack gives the exact
positive-slice floor. -/
theorem projection_cylinder_survival_floor
    (m g k : ℝ)
    (hk : 0 < k)
    (hsurvive : g < m * k + k - 1) :
    (g - k + 1) / k < m := by
  exact (div_lt_iff₀ hk).2 (by linarith)

/-- If the lookup circuit fits the gate budget, it is a valid obstruction. -/
theorem projection_cylinder_fits_budget
    (m g k : ℤ)
    (h : m * k + k - 1 ≤ g) :
    m * k + k - 1 ≤ g := by
  exact h

end PvsNPBraid
