import Mathlib

/-!
# Round 219 RH Abel-edge finite algebra

Honesty boundary:
* This file contains only finite real-algebra shadows used in the Abel-edge note.
* It does not formalize Laplace transforms, infinite sums, zeta zeros, primes,
  dominated convergence, the explicit formula, or RH.
* No theorem below is a Millennium result.
-/

namespace Millennium
namespace Round219RHAbelEdge

/-- After extracting the common edge growth `exp (theta * y)`, a pair of
modes with depth deficits `mu, nu` has total real decay
`delta + mu + nu` under Abel damping. -/
theorem edgeExponentIdentity
    (theta delta mu nu y : ℝ) :
    -(2 * theta + delta) * y
        + (theta - mu) * y
        + (theta - nu) * y
      = -(delta + mu + nu) * y := by
  ring

/-- The squared modulus denominator of the normalized Abel pair kernel is
at least `delta^2` when both depth deficits are nonnegative. -/
theorem abelDenominatorFloor
    (delta mu nu omega : ℝ)
    (hdelta : 0 ≤ delta)
    (hmu : 0 ≤ mu)
    (hnu : 0 ≤ nu) :
    delta ^ 2 ≤ (delta + mu + nu) ^ 2 + omega ^ 2 := by
  have hmn : 0 ≤ mu + nu := add_nonneg hmu hnu
  have hcross : 0 ≤ 2 * delta * (mu + nu) :=
    mul_nonneg (mul_nonneg (by norm_num) hdelta) hmn
  nlinarith [sq_nonneg (mu + nu), sq_nonneg omega]

/-- A same-edge, same-frequency scalar Abel kernel is exactly one. -/
theorem sameEdgeSameFrequencyKernel
    (delta : ℝ) (hdelta : delta ≠ 0) :
    delta / (delta + 0 + 0) = 1 := by
  simpa using (div_self hdelta)

/-- Two coefficients at one identical edge frequency must be grouped before
squaring; their four pair terms equal the square of the grouped amplitude. -/
theorem twoCoefficientGroupedMass (a b : ℝ) :
    a * a + a * b + b * a + b * b = (a + b) ^ 2 := by
  ring

/-- Pairing an even density against the odd coordinate removes the linear
Taylor coefficient. -/
theorem evenFirstMomentPair (u x : ℝ) :
    u * x + (-u) * x = 0 := by
  ring

/-- Exact bookkeeping for the refined diagonal/off-diagonal decomposition. -/
theorem refinedPairCancellationIdentity
    (sigma C A d energyError diagonalError : ℝ) :
    (A / sigma + energyError)
        - (C / sigma ^ 2 + d + diagonalError)
      = -C / sigma ^ 2
        + A / sigma
        - d
        + (energyError - diagonalError) := by
  ring

/-- The ordinary-prime constant produced by the `m = 2` zeta-pole term. -/
theorem ordinaryPrimeConstant (h : ℝ) :
    -(h ^ 4 / 4) / 2 = -(h ^ 4 / 8) := by
  ring

/-- The square of the ordinary-prime constant contributes `h^8 / 64` to
an edge mass at `theta = 0`. -/
theorem ordinaryPrimeConstantSquare (h : ℝ) :
    (-(h ^ 4 / 8)) ^ 2 = h ^ 8 / 64 := by
  ring

#print axioms edgeExponentIdentity
#print axioms abelDenominatorFloor
#print axioms sameEdgeSameFrequencyKernel
#print axioms twoCoefficientGroupedMass
#print axioms evenFirstMomentPair
#print axioms refinedPairCancellationIdentity
#print axioms ordinaryPrimeConstant
#print axioms ordinaryPrimeConstantSquare

end Round219RHAbelEdge
end Millennium
