import Mathlib

/-!
# AO two-Weber close-carrier centered-margin firewall

Finite algebra only.  In the C58 ground/first-excited two-Weber response model,
write `s = sqrt (nOdd / nEven)`.  After removing a common positive amplitude
factor, strict centered positivity is the interval

  s^3 < x < s^4.

This file proves that the two distances to the interval walls have a fixed sum,
that the midpoint balances them optimally, and that any common normalized lower
margin `μ` satisfies the cross-multiplied sharp bound

  2 * μ * (s + 1) ≤ s - 1.

Thus the normalized strict margin must collapse as `s → 1` (carrier
coalescence).  The file does NOT formalize the Albritton--Ożański eigenmodes,
Reynolds-stress asymptotics, the `n^(-3/4)` inner-width law, nonlinear
regeneration, or Navier--Stokes singularity.
-/

namespace Millennium.NavierStokes.AOTwoWeberCloseCarrierMargin

/-- Distance from the lower C58 cone wall. -/
def bMargin (s x : ℚ) : ℚ := x - s^3

/-- Distance from the upper C58 cone wall after dividing the `C` bracket by 3. -/
def cMargin (s x : ℚ) : ℚ := s^4 - x

/-- Sum of the two carrier scales used to normalize a symmetric strict margin. -/
def totalScale (s : ℚ) : ℚ := s^4 + s^3

/-- The two wall distances have a carrier-determined sum independent of the
amplitude-ratio choice `x`. -/
theorem margin_sum (s x : ℚ) :
    bMargin s x + cMargin s x = s^4 - s^3 := by
  simp [bMargin, cMargin]
  ring

/-- The midpoint of the admissible interval balances the two wall distances
exactly, each receiving one half of the available carrier-splitting width. -/
theorem midpoint_balances (s : ℚ) :
    bMargin s ((s^3 + s^4) / 2) = (s^4 - s^3) / 2 ∧
    cMargin s ((s^3 + s^4) / 2) = (s^4 - s^3) / 2 := by
  constructor <;> simp [bMargin, cMargin] <;> ring

/-- If `μ * totalScale s` is a common lower bound for both wall distances,
then twice that common margin cannot exceed the total interval width. -/
theorem common_margin_width_bound
    (s x μ : ℚ)
    (hB : μ * totalScale s ≤ bMargin s x)
    (hC : μ * totalScale s ≤ cMargin s x) :
    2 * μ * totalScale s ≤ s^4 - s^3 := by
  have hsum := add_le_add hB hC
  rw [margin_sum] at hsum
  nlinarith

/-- Sharp cross-multiplied normalized bound.  For positive `s`, the previous
width estimate cancels the positive factor `s^3` and gives
`2 μ (s+1) ≤ s-1`, equivalent (when `s>1`) to
`μ ≤ (s-1)/(2(s+1))`. -/
theorem normalized_margin_collapse_bound
    (s x μ : ℚ) (hs : 0 < s)
    (hB : μ * totalScale s ≤ bMargin s x)
    (hC : μ * totalScale s ≤ cMargin s x) :
    2 * μ * (s + 1) ≤ s - 1 := by
  have h := common_margin_width_bound s x μ hB hC
  have hs3 : 0 < s^3 := pow_pos hs 3
  have hc : s^3 * (2 * μ * (s + 1)) ≤ s^3 * (s - 1) := by
    dsimp [totalScale] at h
    nlinarith
  exact (mul_le_mul_left hs3).mp hc

/-- Equal carriers (`s=1`) force every nonnegative common normalized margin to
be exactly zero.  This is the finite exact-zero endpoint behind the C59
vanishing-threshold obstruction. -/
theorem equal_carrier_nonnegative_margin_zero
    (x μ : ℚ) (hμ : 0 ≤ μ)
    (hB : μ * totalScale 1 ≤ bMargin 1 x)
    (hC : μ * totalScale 1 ≤ cMargin 1 x) :
    μ = 0 := by
  have h := normalized_margin_collapse_bound 1 x μ (by norm_num) hB hC
  norm_num at h
  linarith

#print axioms margin_sum
#print axioms midpoint_balances
#print axioms common_margin_width_bound
#print axioms normalized_margin_collapse_bound
#print axioms equal_carrier_nonnegative_margin_zero

end Millennium.NavierStokes.AOTwoWeberCloseCarrierMargin
