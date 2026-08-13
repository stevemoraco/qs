import Mathlib

/-!
Finite algebraic core for the RH prime-prefix discrepancy-energy ledger.

This file does not formalize primes, Chebyshev theta, integrals, Johnston's
criterion, or RH. It only certifies the exact quadratic jump identities and
one-step weighted accounting algebra used by the human note.
-/

namespace RHDiscrepancyEnergyLedgerFinite

/-- The local Johnston kick equals minus the jump of quadratic discrepancy
energy when a prime jump of size `L` sends `Dminus` to `Dminus-L`. -/
theorem kick_eq_negative_energy_jump
    (Dminus L : ℝ) :
    (L * Dminus - L^2 / 2)
      = -(((Dminus - L)^2 / 2) - (Dminus^2 / 2)) := by
  ring

/-- Equivalent orientation: the quadratic energy jump is exactly `-h`. -/
theorem energy_jump_eq_negative_kick
    (Dminus L : ℝ) :
    ((Dminus - L)^2 / 2) - (Dminus^2 / 2)
      = -(L * Dminus - L^2 / 2) := by
  ring

/-- Clearing the threshold defect used in the prime-prefix sign test. -/
theorem threshold_defect_factorization
    (q L h : ℝ) :
    4 * q * (h / L) + L^2 / 4
      = (4 * q / L) * (h + L^3 / (16 * q)) := by
  field_simp
  ring

/-- If a weighted energy has continuous contribution `cont`, dissipation
`diss`, boundary increment `bdry`, and prime jumps `-sumKick`, then solving the
ledger for the signed kick sum is pure algebra. -/
theorem solve_weighted_ledger
    (cont diss bdry sumKick : ℝ)
    (h : bdry = cont - diss - sumKick) :
    sumKick = cont - diss - bdry := by
  linarith

/-- The reverse orientation used to reconstruct critical reserve from the
signed prime cocycle, dissipation, and boundary energy. -/
theorem reconstruct_continuous_reserve
    (cont diss bdry sumKick : ℝ)
    (h : sumKick = cont - diss - bdry) :
    cont = sumKick + diss + bdry := by
  linarith

/-- A signed first moment does not algebraically control a quadratic energy:
this concrete witness has zero signed sum but positive square sum. -/
theorem signed_first_moment_does_not_kill_square :
    ((1 : ℝ) + (-1)) = 0 ∧ (1 : ℝ)^2 + (-1 : ℝ)^2 = 2 := by
  norm_num

#print axioms kick_eq_negative_energy_jump
#print axioms energy_jump_eq_negative_kick
#print axioms threshold_defect_factorization
#print axioms solve_weighted_ledger
#print axioms reconstruct_continuous_reserve
#print axioms signed_first_moment_does_not_kill_square

end RHDiscrepancyEnergyLedgerFinite
