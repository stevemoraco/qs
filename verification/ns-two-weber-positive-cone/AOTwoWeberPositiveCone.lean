import Mathlib

/-!
# AO two-Weber positive centered-response cone

Finite algebra only.  The analytic input from the AO regeneration calculation
assigns one odd Weber self-response and one even Weber self-response the
normalized centered brackets encoded below.  This file verifies the exact
feasibility arithmetic and one explicit carrier-separated witness.

It does NOT formalize the Albritton--Ożański eigenmodes, Reynolds-stress
asymptotics, Fourier-sector decoupling, nonlinear modulation, regeneration, or
Navier--Stokes singularity.
-/

namespace Millennium.NavierStokes.AOTwoWeberPositiveCone

/-- Normalized `b`-response bracket for one odd and one even Weber self-response.
`A` is the positive carrier factor corresponding to `(nOdd/nEven)^(3/2)` in the
analytic application. -/
def bBracket (ellOdd κ hOdd A hEven : ℚ) : ℚ :=
  hEven - ellOdd * κ * hOdd * A

/-- Normalized `C = Lambda''` response bracket.  `B` is the positive carrier
factor corresponding to `(nOdd/nEven)^2` in the analytic application. -/
def cBracket (ellOdd ellEven κ hOdd B hEven : ℚ) : ℚ :=
  (ellOdd^2 + 2) * κ * hOdd * B - ellEven * hEven

/-- If the even-mode amplitude weight lies strictly above the `b` lower bound
and strictly below the `C` upper bound, both centered response brackets are
strictly positive. -/
theorem positive_response_of_interval
    (ellOdd ellEven κ hOdd A B hEven : ℚ)
    (hb : ellOdd * κ * hOdd * A < hEven)
    (hC : ellEven * hEven < (ellOdd^2 + 2) * κ * hOdd * B) :
    0 < bBracket ellOdd κ hOdd A hEven ∧
    0 < cBracket ellOdd ellEven κ hOdd B hEven := by
  constructor <;> simp [bBracket, cBracket] <;> linarith

/-- Exact first-two-Weber carrier-separated witness from the research ledger.
For `ellOdd=1`, `ellEven=3`, carrier ratio `nOdd/nEven=4`, the normalized
carrier factors are `A=8`, `B=16`.  Choosing `hEven=12*κ*hOdd` leaves positive
brackets `4*κ*hOdd` and `12*κ*hOdd`. -/
theorem m1_m2_carrier4_weight12
    (κ h : ℚ) (hκ : 0 < κ) (hh : 0 < h) :
    bBracket 1 κ h 8 (12 * κ * h) = 4 * κ * h ∧
    cBracket 1 3 κ h 16 (12 * κ * h) = 12 * κ * h ∧
    0 < bBracket 1 κ h 8 (12 * κ * h) ∧
    0 < cBracket 1 3 κ h 16 (12 * κ * h) := by
  constructor
  · simp [bBracket]
    ring
  constructor
  · simp [cBracket]
    ring
  constructor
  · simp [bBracket]
    nlinarith
  · simp [cBracket]
    nlinarith

/-- The same witness has the strict amplitude interval recorded in the human
proof: `8*κ*h < 12*κ*h < 16*κ*h`. -/
theorem m1_m2_carrier4_strict_interval
    (κ h : ℚ) (hκ : 0 < κ) (hh : 0 < h) :
    8 * κ * h < 12 * κ * h ∧
    12 * κ * h < 16 * κ * h := by
  constructor <;> nlinarith

/-- At equal carriers the first two Weber families are exactly on the centered
cone boundary: their lower and upper amplitude thresholds coincide at
`κ*hOdd`.  This formalizes the reason a strict carrier split is useful. -/
theorem m1_m2_equal_carrier_boundary (κ h : ℚ) :
    1 * κ * h * 1 = ((1^2 + 2) / 3) * κ * h * 1 := by
  ring

#print axioms positive_response_of_interval
#print axioms m1_m2_carrier4_weight12
#print axioms m1_m2_carrier4_strict_interval
#print axioms m1_m2_equal_carrier_boundary

end Millennium.NavierStokes.AOTwoWeberPositiveCone
