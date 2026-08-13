import Mathlib

namespace NSNonlinearSidebandBall

/-- Exact Riccati drift at the proposed invariant radius `R=2ε/δ`. -/
theorem boundary_drift_identity
    {delta epsilon M : ℝ} (hdelta : delta ≠ 0) :
    -delta * (2 * epsilon / delta) + epsilon +
        M * (2 * epsilon / delta) ^ 2 =
      -epsilon + 4 * M * epsilon ^ 2 / delta ^ 2 := by
  field_simp [hdelta]
  ring

/-- The proposed radius is nonnegative for nonnegative forcing and positive
net damping. -/
theorem radius_nonnegative
    {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) :
    0 ≤ 2 * epsilon / delta := by
  positivity

/-- Under the discriminant margin, the quadratic contribution at the boundary
is strictly smaller than the residual forcing. -/
theorem quadratic_boundary_below_forcing
    {delta epsilon M : ℝ}
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hdisc : 4 * M * epsilon < delta ^ 2) :
    4 * M * epsilon ^ 2 / delta ^ 2 < epsilon := by
  have hdelta2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  apply (div_lt_iff₀ hdelta2).2
  have hmul := mul_lt_mul_of_pos_right hdisc hepsilon
  nlinarith

/-- Exact strict inward-pointing condition for the Riccati barrier. -/
theorem boundary_drift_negative
    {delta epsilon M : ℝ}
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hdisc : 4 * M * epsilon < delta ^ 2) :
    -delta * (2 * epsilon / delta) + epsilon +
        M * (2 * epsilon / delta) ^ 2 < 0 := by
  rw [boundary_drift_identity (ne_of_gt hdelta)]
  have hquad := quadratic_boundary_below_forcing hdelta hepsilon hdisc
  nlinarith

/-- At the proposed radius, the net linear damping is exactly twice the source
size. -/
theorem linear_boundary_balance
    {delta epsilon : ℝ} (hdelta : delta ≠ 0) :
    delta * (2 * epsilon / delta) = 2 * epsilon := by
  field_simp [hdelta]

#print axioms boundary_drift_identity
#print axioms radius_nonnegative
#print axioms quadratic_boundary_below_forcing
#print axioms boundary_drift_negative
#print axioms linear_boundary_balance

end NSNonlinearSidebandBall
