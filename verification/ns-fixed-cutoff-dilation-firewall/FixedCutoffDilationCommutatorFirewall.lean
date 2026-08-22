import Mathlib

namespace Millennium.NavierStokes

/-!
# Fixed-cutoff dilation commutator firewall

For a localized quotient, a mass-preserving dilation has the advertised pure
homogeneous slopes only when the cutoff is dilated with the profile or when all
fixed-cutoff commutators are proved to vanish.  At a fixed cutoff the exact
first-variation ledger has the form

`transferSlope = 3 * J + cJ`,
`visibilitySlope = 4 * A + cA`,

where the factors `3` and `4` are twice the degrees `3/2` and `2`, and `cJ,cA`
are the doubled cutoff commutators.  Stationarity therefore yields

`3*J + cJ = Lambda * (4*A + cA)`,

not the pure identity `3*J = 4*Lambda*A` unless the additional commutator
balance `cJ = Lambda*cA` is proved.

This file verifies only that exact finite algebra and its smallest
counterexample.  The analytic change-of-variables formula identifying `cJ,cA`
for the Navier--Stokes endpoint functional is recorded in the companion human
note.  No PDE or Clay theorem is asserted here.
-/

/-- Doubled first-variation slope of the localized transfer. -/
noncomputable def localizedTransferSlope (J cJ : ℝ) : ℝ := 3 * J + cJ

/-- Doubled first-variation slope of the localized visibility. -/
noncomputable def localizedVisibilitySlope (A cA : ℝ) : ℝ := 4 * A + cA

/-- The exact difference between the localized stationarity residual and the
pure-homogeneity residual is the cutoff-commutator mismatch. -/
theorem localized_stationarity_residual_decomposition
    (J A Lambda cJ cA : ℝ) :
    (localizedTransferSlope J cJ -
        Lambda * localizedVisibilitySlope A cA) -
      (3 * J - 4 * Lambda * A) =
        cJ - Lambda * cA := by
  unfold localizedTransferSlope localizedVisibilitySlope
  ring

/-- Exact stationarity ledger with the commutator terms kept visible. -/
theorem localized_stationarity_ledger
    {J A Lambda cJ cA : ℝ}
    (hstationary :
      localizedTransferSlope J cJ =
        Lambda * localizedVisibilitySlope A cA) :
    3 * J - 4 * Lambda * A = Lambda * cA - cJ := by
  unfold localizedTransferSlope localizedVisibilitySlope at hstationary
  linarith

/-- The pure dilation identity is recovered only after the additional
commutator-balance theorem is supplied. -/
theorem localized_stationarity_with_balanced_commutators
    {J A Lambda cJ cA : ℝ}
    (hstationary :
      localizedTransferSlope J cJ =
        Lambda * localizedVisibilitySlope A cA)
    (hbalance : cJ = Lambda * cA) :
    3 * J = 4 * Lambda * A := by
  have hledger := localized_stationarity_ledger hstationary
  rw [hbalance] at hledger
  linarith

/-- Smallest exact counterexample: quotient saturation and genuine localized
stationarity can both hold while the pure `3`-versus-`4` identity fails, because
a nonzero cutoff commutator pays the missing unit. -/
theorem localized_stationarity_does_not_force_pure_homogeneity :
    ∃ (J A Lambda cJ cA : ℝ),
      0 < Lambda ∧
      A = 1 ∧
      J = Lambda * A ∧
      localizedTransferSlope J cJ =
        Lambda * localizedVisibilitySlope A cA ∧
      3 * J ≠ 4 * Lambda * A := by
  refine ⟨1, 1, 1, 1, 0, by norm_num, rfl, by norm_num, ?_, by norm_num⟩
  norm_num [localizedTransferSlope, localizedVisibilitySlope]

/-- Even pointwise quotient saturation does not provide either independent
amplitude Euler equation.  This is the exact scalar shadow of the separate
admissibility/extremality obligation for the amplitude curves. -/
theorem quotient_saturation_does_not_force_amplitude_euler_pair :
    ∃ (J1 K V betaW Lambda : ℝ),
      0 < Lambda ∧ 0 < V ∧ 0 < betaW ∧
      J1 - K = Lambda * (V + betaW) ∧
      3 * J1 - K ≠ 2 * Lambda * V ∧
      -K ≠ Lambda * betaW := by
  refine ⟨3, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  all_goals norm_num

#print axioms localized_stationarity_residual_decomposition
#print axioms localized_stationarity_ledger
#print axioms localized_stationarity_with_balanced_commutators
#print axioms localized_stationarity_does_not_force_pure_homogeneity
#print axioms quotient_saturation_does_not_force_amplitude_euler_pair

end Millennium.NavierStokes
