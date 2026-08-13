import Mathlib

/-!
Finite cancellation theorem for the RH prime-prefix Bregman reserve and
critical discrepancy-energy ledger.

The file assumes the already-derived analytic identities as equalities between
real scalars. It does not define primes, theta, Stieltjes integrals, discrepancy,
or RH.
-/

namespace RHBregmanLedgerCollapse

/-- Summing the one-prime split and substituting the weighted discrepancy ledger
makes the accumulated Bregman reserve an exact endpoint-corrected copy of the
continuous dissipation. -/
theorem accumulated_reserve_identity
    (F F2 M Q Q2 I W W2 kickSum slackSum : ℝ)
    (hPrefix : F = F2 + (1 / 2 : ℝ) * kickSum + slackSum)
    (hLedger : kickSum = 2 * M - (3 / 4 : ℝ) * I - W + W2)
    (hEndpoint : F = M - Q)
    (hBase : F2 = -Q2) :
    slackSum =
      (3 / 8 : ℝ) * I + (1 / 2 : ℝ) * (W - W2) + Q2 - Q := by
  linarith

/-- Equivalent no-double-counting form: endpoint AM-GM debt plus accumulated
local slack equals the continuous dissipation and boundary-energy budget. -/
theorem no_double_counting_identity
    (F F2 M Q Q2 I W W2 kickSum slackSum : ℝ)
    (hPrefix : F = F2 + (1 / 2 : ℝ) * kickSum + slackSum)
    (hLedger : kickSum = 2 * M - (3 / 4 : ℝ) * I - W + W2)
    (hEndpoint : F = M - Q)
    (hBase : F2 = -Q2) :
    Q + slackSum =
      Q2 + (3 / 8 : ℝ) * I + (1 / 2 : ℝ) * (W - W2) := by
  have h := accumulated_reserve_identity
    F F2 M Q Q2 I W W2 kickSum slackSum
    hPrefix hLedger hEndpoint hBase
  linarith

/-- Positivity of the accumulated slack yields only the corresponding endpoint
inequality; it does not by itself imply positivity of the prime-prefix target. -/
theorem slack_nonnegative_endpoint_inequality
    (F F2 M Q Q2 I W W2 kickSum slackSum : ℝ)
    (hPrefix : F = F2 + (1 / 2 : ℝ) * kickSum + slackSum)
    (hLedger : kickSum = 2 * M - (3 / 4 : ℝ) * I - W + W2)
    (hEndpoint : F = M - Q)
    (hBase : F2 = -Q2)
    (hSlack : 0 ≤ slackSum) :
    Q ≤ Q2 + (3 / 8 : ℝ) * I + (1 / 2 : ℝ) * (W - W2) := by
  have h := no_double_counting_identity
    F F2 M Q Q2 I W W2 kickSum slackSum
    hPrefix hLedger hEndpoint hBase
  linarith

/-- If `r=sqrt(p)` and `s=sqrt(theta(p))`, then the endpoint AM-GM debt
minus half the weighted quadratic boundary energy is one signed cubic trace. -/
theorem endpoint_cubic_factorization
    (r s : ℝ)
    (hr : r ≠ 0) :
    (r - s) ^ 2 / r -
        ((r - s) ^ 2 * (r + s) ^ 2 / (2 * r ^ 3)) / 2 =
      (r - s) ^ 3 * (3 * r + s) / (4 * r ^ 3) := by
  field_simp [hr]
  ring

#print axioms accumulated_reserve_identity
#print axioms no_double_counting_identity
#print axioms slack_nonnegative_endpoint_inequality
#print axioms endpoint_cubic_factorization

end RHBregmanLedgerCollapse
