import Millennium.Hodge.HodgeR3BinaryCubicIndexForm

/-!
# Hodge r=3 square-form μ-elimination finite core

Finite scalar identities only.  The geometric statement that these scalars are
coefficients of binary forms on `P¹`, and the required global divisibility by
`beta`, are deliberately not encoded here.
-/

namespace Millennium.Hodge.R3MuElimination

/-- The two square-form reconstruction equations eliminate `mu` to one exact
quadratic resultant identity. -/
theorem eliminate_mu_square
    (A B H J mu beta : ℝ)
    (hA : A = H + 2 * mu * beta + beta^4 / 3)
    (hB : B = J + mu^2 - (beta^2 / 3) * H - beta^6 / 27) :
    (A - H - beta^4 / 3)^2
      = 4 * beta^2 *
          (B - J + (beta^2 / 3) * H + beta^6 / 27) := by
  rw [hA, hB]
  ring

/-- On the `beta = 0` boundary, the first reconstruction equation forces
`H = A`. -/
theorem beta_zero_forces_H
    (A H mu beta : ℝ)
    (hbeta : beta = 0)
    (hA : A = H + 2 * mu * beta + beta^4 / 3) :
    H = A := by
  subst beta
  norm_num at hA ⊢
  linarith

/-- On the `beta = 0` boundary, the second reconstruction equation is exactly
`B - J = mu^2`. -/
theorem beta_zero_square_boundary
    (B J H mu beta : ℝ)
    (hbeta : beta = 0)
    (hB : B = J + mu^2 - (beta^2 / 3) * H - beta^6 / 27) :
    B - J = mu^2 := by
  subst beta
  norm_num at hB ⊢
  linarith

/-- If `beta` is nonzero, the first reconstruction equation recovers `mu`
pointwise.  The global binary-form version additionally requires polynomial
divisibility, which is outside this scalar firewall. -/
theorem recover_mu_when_beta_ne_zero
    (A H mu beta : ℝ)
    (hbeta : beta ≠ 0)
    (hA : A = H + 2 * mu * beta + beta^4 / 3) :
    mu = (A - H - beta^4 / 3) / (2 * beta) := by
  field_simp [hbeta]
  nlinarith [hA]

#print axioms eliminate_mu_square
#print axioms beta_zero_forces_H
#print axioms beta_zero_square_boundary
#print axioms recover_mu_when_beta_ne_zero

end Millennium.Hodge.R3MuElimination
