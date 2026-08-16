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

def bBracket (ellOdd κ hOdd A hEven : ℚ) : ℚ :=
  hEven - ellOdd * κ * hOdd * A

def cBracket (ellOdd ellEven κ hOdd B hEven : ℚ) : ℚ :=
  (ellOdd^2 + 2) * κ * hOdd * B - ellEven * hEven

theorem positive_response_of_interval
    (ellOdd ellEven κ hOdd A B hEven : ℚ)
    (hb : ellOdd * κ * hOdd * A < hEven)
    (hC : ellEven * hEven < (ellOdd^2 + 2) * κ * hOdd * B) :
    0 < bBracket ellOdd κ hOdd A hEven ∧
    0 < cBracket ellOdd ellEven κ hOdd B hEven := by
  constructor <;> simp [bBracket, cBracket] <;> linarith

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

theorem m1_m2_carrier4_strict_interval
    (κ h : ℚ) (hκ : 0 < κ) (hh : 0 < h) :
    8 * κ * h < 12 * κ * h ∧
    12 * κ * h < 16 * κ * h := by
  constructor <;> nlinarith

theorem m1_m2_equal_carrier_boundary (κ h : ℚ) :
    1 * κ * h * 1 = ((1^2 + 2) / 3) * κ * h * 1 := by
  ring

#print axioms positive_response_of_interval
#print axioms m1_m2_carrier4_weight12
#print axioms m1_m2_carrier4_strict_interval
#print axioms m1_m2_equal_carrier_boundary

end Millennium.NavierStokes.AOTwoWeberPositiveCone
