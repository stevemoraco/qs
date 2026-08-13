import Mathlib

/-!
# RH discrepancy-energy gap-drift finite algebra

Honesty boundary:
* These declarations prove only polynomial identities over the reals.
* They do not formalize primes, theta, logarithms, Bregman positivity,
  Johnston's theorem, zeta zeros, or RH.
* This source has not been compiled in the current sandbox.
-/

namespace RHRobinEnergyGapDrift

/-- At one fixed arrival coordinate, subtracting the prime weight changes
quadratic discrepancy energy by the negative Johnston scalar. -/
theorem sameCoordinateEnergyJump
    (d gap ell : ℝ) :
    ((d + gap - ell) ^ 2 / 2 - (d + gap) ^ 2 / 2)
      = -(ell * (d + gap) - ell ^ 2 / 2) := by
  ring

/-- Moving from the preceding prime coordinate to the new pre-arrival
coordinate contributes the exact gap-transport energy. -/
theorem gapTransport
    (d gap : ℝ) :
    (d + gap) ^ 2 / 2 - d ^ 2 / 2
      = gap * d + gap ^ 2 / 2 := by
  ring

/-- The true endpoint-to-endpoint energy increment is local arrival loss plus
the coordinate-transport term. -/
theorem endpointEnergyIncrement
    (d gap ell : ℝ) :
    (d + gap - ell) ^ 2 / 2 - d ^ 2 / 2
      = gap * d + gap ^ 2 / 2
        - (ell * (d + gap) - ell ^ 2 / 2) := by
  ring

/-- Substituting the corrected endpoint energy into a local weighted
Bregman increment necessarily retains the gap-transport term. -/
theorem correctedWeightedIncrement
    (deltaA weight slack d gap ell : ℝ)
    (hlocal :
      deltaA = weight * (ell * (d + gap) - ell ^ 2 / 2) + slack) :
    deltaA
      = -weight *
          ((d + gap - ell) ^ 2 / 2 - d ^ 2 / 2)
        + weight * (gap * d + gap ^ 2 / 2)
        + slack := by
  rw [hlocal]
  ring

#check sameCoordinateEnergyJump
#check gapTransport
#check endpointEnergyIncrement
#check correctedWeightedIncrement

#print axioms sameCoordinateEnergyJump
#print axioms gapTransport
#print axioms endpointEnergyIncrement
#print axioms correctedWeightedIncrement

end RHRobinEnergyGapDrift
