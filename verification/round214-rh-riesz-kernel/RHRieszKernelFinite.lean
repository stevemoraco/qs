import Mathlib

/-!
# Round 214 RH Riesz-kernel finite cores

This file formalizes only finite rational evaluations, polynomial positivity,
a finite weighted-sign implication, and a scalar noncancellation fact for a
Riesz Laplace multiplier. It does not formalize the Riemann zeta function,
Weil's functional, Laplace transforms, Landau's theorem, prime sums, or RH.
-/

namespace Millennium
namespace Round214RH

/-- Positive part on the rationals. -/
def positivePart (x : ℚ) : ℚ := max x 0

/-- The exact base-scale value `mu(1)^2`. -/
def muSqOne : ℚ := 3570 / 991

/-- One shifted truncated-power summand in the base-scale physical kernel. -/
def hOneAtom (t shift : ℚ) : ℚ :=
  let y := positivePart (t + shift)
  y ^ 3 / 6 + (muSqOne - 1 / 4) * y ^ 5 / 120 -
    muSqOne * y ^ 7 / 20160

/-- The base-scale physical kernel, written as the exact expanded eighth
finite-difference sum with binomial coefficients. -/
def hOne (t : ℚ) : ℚ :=
  hOneAtom t 4 - 8 * hOneAtom t 3 + 28 * hOneAtom t 2 -
    56 * hOneAtom t 1 + 70 * hOneAtom t 0 -
    56 * hOneAtom t (-1) + 28 * hOneAtom t (-2) -
    8 * hOneAtom t (-3) + hOneAtom t (-4)

/-- The normalized base-scale kernel `a^4 d(a) h_a / 16` at `a=1`. -/
def normalizedKernelOne (t : ℚ) : ℚ := (991 / 16) * hOne t

/-- Exact negative lobe value. -/
theorem normalizedKernelOne_at_one :
    normalizedKernelOne 1 = -10257 / 128 := by
  norm_num [normalizedKernelOne, hOne, hOneAtom, positivePart, muSqOne]

/-- Exact positive lobe value. -/
theorem normalizedKernelOne_at_two :
    normalizedKernelOne 2 = 201 / 5 := by
  norm_num [normalizedKernelOne, hOne, hOneAtom, positivePart, muSqOne]

/-- The normalized physical kernel already changes sign at the base scale. -/
theorem normalizedKernelOne_sign_change :
    normalizedKernelOne 1 < 0 ∧ 0 < normalizedKernelOne 2 := by
  rw [normalizedKernelOne_at_one, normalizedKernelOne_at_two]
  norm_num

/-- Shifted numerator controlling the value of the normalized kernel at `t=1`. -/
def pOneShifted (x : ℚ) : ℚ :=
  3152 * x ^ 7 + 22064 * x ^ 6 + 181812 * x ^ 5 +
  604917 * x ^ 4 + 1317648 * x ^ 3 + 1406429 * x ^ 2 +
  747402 * x + 123084

/-- The shifted numerator is strictly positive on the nonnegative axis. -/
theorem pOneShifted_pos (x : ℚ) (hx : 0 ≤ x) :
    0 < pOneShifted x := by
  dsimp [pOneShifted]
  positivity

/-- The exact crude upper bound used for the `t=2`, `0<=x<=1/8` interval. -/
def pTwoCrudeUpperBound : ℚ :=
  273 * (1 / 8 : ℚ) ^ 9 + 35723 * (1 / 8 : ℚ) ^ 5 +
  599042 * (1 / 8 : ℚ) ^ 4 + 540413 * (1 / 8 : ℚ) ^ 3 +
  231307 * (1 / 8 : ℚ) ^ 2 - 9648

/-- Exact endpoint arithmetic certificate for the positive-monomial bound. -/
theorem pTwoCrudeUpperBound_value :
    pTwoCrudeUpperBound = -648404946671 / 134217728 := by
  norm_num [pTwoCrudeUpperBound]

/-- In particular, the crude upper bound is strictly negative. -/
theorem pTwoCrudeUpperBound_neg : pTwoCrudeUpperBound < 0 := by
  rw [pTwoCrudeUpperBound_value]
  norm_num

/-- A positive weighted combination of channels that are jointly negative at
one sample and jointly nonnegative at another retains the sign change. This is
a two-channel finite shadow of the causal-smoothing obstruction. -/
theorem positive_two_channel_average_retains_sign_change
    (w₁ w₂ n₁ n₂ p₁ p₂ : ℚ)
    (hw₁ : 0 < w₁) (hw₂ : 0 ≤ w₂)
    (hn₁ : n₁ < 0) (hn₂ : n₂ ≤ 0)
    (hp₁ : 0 < p₁) (hp₂ : 0 ≤ p₂) :
    w₁ * n₁ + w₂ * n₂ < 0 ∧
      0 < w₁ * p₁ + w₂ * p₂ := by
  constructor
  · have hfirst : w₁ * n₁ < 0 := mul_neg_of_pos_of_neg hw₁ hn₁
    have hsecond : w₂ * n₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw₂ hn₂
    linarith
  · have hfirst : 0 < w₁ * p₁ := mul_pos hw₁ hp₁
    have hsecond : 0 ≤ w₂ * p₂ := mul_nonneg hw₂ hp₂
    linarith

/-- Multiplication of a nonzero pole residue by the finite Riesz Laplace
multiplier `s^(-m)` cannot cancel a pole away from `s=0`. -/
theorem riesz_multiplier_preserves_nonzero_residue
    (s residue : ℂ) (m : ℕ)
    (hs : s ≠ 0) (hresidue : residue ≠ 0) :
    residue / s ^ m ≠ 0 := by
  exact div_ne_zero hresidue (pow_ne_zero m hs)

#print axioms normalizedKernelOne_at_one
#print axioms normalizedKernelOne_at_two
#print axioms normalizedKernelOne_sign_change
#print axioms pOneShifted_pos
#print axioms pTwoCrudeUpperBound_value
#print axioms pTwoCrudeUpperBound_neg
#print axioms positive_two_channel_average_retains_sign_change
#print axioms riesz_multiplier_preserves_nonzero_residue

end Round214RH
end Millennium
