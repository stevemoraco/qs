import Mathlib

namespace RHEndpointPolynomialRemoteFinite

/-- One summand in the elementary Legendre/Bessel remote-band budget. -/
def bandTerm (k : ℕ) : ℚ :=
  2 * (4 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) ^ 2

/-- The finite budget appearing after bounding every spherical Bessel feature. -/
def bandBudget (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, bandTerm k

/-- Exact closed form for the remote-band budget. -/
theorem bandBudget_closed (N : ℕ) :
    bandBudget N =
      (4 * (N : ℚ) * ((N : ℚ) + 1) *
        (6 * (N : ℚ) ^ 2 + 4 * (N : ℚ) - 1)) / 3 := by
  induction N with
  | zero => simp [bandBudget]
  | succ N ih =>
      unfold bandBudget at ih ⊢
      rw [Finset.sum_range_succ, ih]
      simp [bandTerm]
      push_cast
      ring

/-- The quadratic threshold inequality used to turn the explicit feature lower
    bound into the clean value `1/2`. -/
theorem defect_at_least_half_of_quadratic
    {xi B : ℝ}
    (hxi : 0 < xi)
    (hquad : xi ^ 2 - xi - 2 * B ≥ 0) :
    1 - 1 / (2 * xi) - B / xi ^ 2 ≥ (1 : ℝ) / 2 := by
  have hxi0 : xi ≠ 0 := ne_of_gt hxi
  have hxi2 : 0 < xi ^ 2 := sq_pos_of_pos hxi
  field_simp [hxi0]
  nlinarith

/-- If the trace pays at least a fixed fraction of remote negative mass, and
    that remote mass already exceeds the full complement budget, the trace
    reaches the budget. -/
theorem remote_mass_forces_trace_budget
    {trace remote denom budget : ℝ}
    (hdenom : 0 < denom)
    (htrace : remote / denom ≤ trace)
    (hmass : denom * budget ≤ remote) :
    budget ≤ trace := by
  have hbudget : budget ≤ remote / denom := by
    exact (le_div_iff₀ hdenom).2 hmass
  exact hbudget.trans htrace

/-- A nonpositive complement margin follows once the trace reaches the baseline
    budget. -/
theorem trace_budget_kills_margin
    {gamma traceRoot : ℝ}
    (h : gamma ≤ traceRoot) :
    gamma - traceRoot ≤ 0 := by
  linarith

#print axioms bandBudget_closed
#print axioms defect_at_least_half_of_quadratic
#print axioms remote_mass_forces_trace_budget
#print axioms trace_budget_kills_margin

end RHEndpointPolynomialRemoteFinite
