import Mathlib

namespace NSPlaneHolonomyQuadratic

/-- Equal subdivision preserves the total first-order displacement. -/
theorem equal_step_linear
    {A N : ℝ} (hN : N ≠ 0) :
    N * (A / N) = A := by
  calc
    N * (A / N) = A * (N / N) := by ring
    _ = A := by rw [div_self hN, mul_one]

/-- The corresponding sum of equal quadratic local costs is `A²/N`. -/
theorem equal_step_quadratic
    {A N : ℝ} (hN : N ≠ 0) :
    N * (A / N) ^ 2 = A ^ 2 / N := by
  field_simp [hN]
  <;> ring

/-- Once the number of subdivisions exceeds the quadratic budget ratio,
    the total quadratic local cost is strictly below the requested budget. -/
theorem equal_step_quadratic_lt
    {A N ε : ℝ} (hN : 0 < N)
    (hbudget : A ^ 2 < ε * N) :
    N * (A / N) ^ 2 < ε := by
  rw [equal_step_quadratic (ne_of_gt hN)]
  exact (div_lt_iff₀ hN).2 hbudget

/-- A scalar shadow of the homogeneity mismatch: a fixed first-order total can
    coexist with an arbitrarily small quadratic ledger after enough equal
    subdivision, once the explicit strict budget inequality is supplied. -/
theorem fixed_total_small_quadratic_ledger
    {A N ε : ℝ} (hN : 0 < N)
    (hbudget : A ^ 2 < ε * N) :
    N * (A / N) = A ∧ N * (A / N) ^ 2 < ε := by
  constructor
  · exact equal_step_linear (ne_of_gt hN)
  · exact equal_step_quadratic_lt hN hbudget

#print axioms equal_step_linear
#print axioms equal_step_quadratic
#print axioms equal_step_quadratic_lt
#print axioms fixed_total_small_quadratic_ledger

end NSPlaneHolonomyQuadratic
