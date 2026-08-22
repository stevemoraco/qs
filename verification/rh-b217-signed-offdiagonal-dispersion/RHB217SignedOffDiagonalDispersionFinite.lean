import Mathlib

/-!
# B217 finite signed off-diagonal dispersion core

Finite algebra only.

This file formalizes the load-bearing scalar transfers used after the human
B217 Haar-energy expansion has already supplied

`energy = diagonal + offDiagonal`.

It does **not** formalize primes, logarithms, Haar integrals, B129/B131,
PNT, zeta, Xi, Deng--Yang--Lu, B46, RH, or not-RH.
-/

namespace RHB217SignedOffDiagonalDispersionFinite

/-- A nonnegative full energy forces the signed off-diagonal term to be no
smaller than minus the diagonal. -/
theorem offDiagonal_lower_of_nonneg_energy
    (diagonal offDiagonal : ℝ)
    (hEnergy : 0 ≤ diagonal + offDiagonal) :
    -diagonal ≤ offDiagonal := by
  linarith

/-- If the diagonal and signed off-diagonal pieces have separate upper bounds,
then their full energy has the summed upper bound. -/
theorem energy_upper_of_piece_bounds
    (diagonal offDiagonal diagonalBound offDiagonalBound : ℝ)
    (hDiagonal : diagonal ≤ diagonalBound)
    (hOff : offDiagonal ≤ offDiagonalBound) :
    diagonal + offDiagonal ≤ diagonalBound + offDiagonalBound := by
  linarith

/-- If `energy = diagonal + offDiagonal` with nonnegative diagonal, any upper
bound for the full energy is automatically an upper bound for the signed
off-diagonal term. -/
theorem offDiagonal_upper_of_energy_upper
    (energy diagonal offDiagonal upper : ℝ)
    (hDecomp : energy = diagonal + offDiagonal)
    (hDiagonal : 0 ≤ diagonal)
    (hEnergy : energy ≤ upper) :
    offDiagonal ≤ upper := by
  linarith

/-- Conversely, an upper bound for the diagonal together with an upper bound
for the signed off-diagonal term controls the full energy. -/
theorem energy_upper_of_offDiagonal_upper
    (energy diagonal offDiagonal diagonalBound offDiagonalBound : ℝ)
    (hDecomp : energy = diagonal + offDiagonal)
    (hDiagonal : diagonal ≤ diagonalBound)
    (hOff : offDiagonal ≤ offDiagonalBound) :
    energy ≤ diagonalBound + offDiagonalBound := by
  linarith

/-- Splitting a signed correlation into positive and negative masses records
that only their difference enters the signed target. -/
theorem signed_split
    (positiveMass negativeMass : ℝ) :
    positiveMass - negativeMass + negativeMass = positiveMass := by
  ring

/-- Hostile scalar ledger: arbitrarily large positive and negative pieces may
have a fixed signed difference.  This is the finite shadow of the B217
absolute-value firewall. -/
theorem large_parts_small_difference (M : ℝ) :
    (M + 1) - M = 1 := by
  ring

/-- If both sign masses dominate a common baseline, their absolute-value sum
must dominate twice that baseline even though their signed difference may be
small. -/
theorem absolute_mass_lower
    (positiveMass negativeMass baseline : ℝ)
    (hPos : baseline ≤ positiveMass)
    (hNeg : baseline ≤ negativeMass) :
    2 * baseline ≤ positiveMass + negativeMass := by
  linarith

#print axioms offDiagonal_lower_of_nonneg_energy
#print axioms energy_upper_of_piece_bounds
#print axioms offDiagonal_upper_of_energy_upper
#print axioms energy_upper_of_offDiagonal_upper
#print axioms signed_split
#print axioms large_parts_small_difference
#print axioms absolute_mass_lower

end RHB217SignedOffDiagonalDispersionFinite
