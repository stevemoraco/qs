import Mathlib

namespace BSDIsogenySelmerRatioLedger

/-- Integer valuation form of Cassels' isogeny product formula: the global
Selmer-ratio exponent is the sum of the normalized `p`/infinity contribution
and the away-from-`p` Tamagawa-ratio exponent. -/
theorem away_tamagawa_from_cassels
    {selmerRatio localPacket awayTamagawa : ℤ}
    (hcassels : selmerRatio = localPacket + awayTamagawa) :
    awayTamagawa = selmerRatio - localPacket := by
  omega

/-- The proposed Eisenstein-index/Tamagawa identity is exactly equivalent to
a global Selmer-ratio identity after the local packet is recorded. -/
theorem eisenstein_tamagawa_iff_selmer_balance
    {eisensteinIndex selmerRatio localPacket awayTamagawa : ℤ}
    (hcassels : selmerRatio = localPacket + awayTamagawa) :
    eisensteinIndex = awayTamagawa ↔
      selmerRatio = eisensteinIndex + localPacket := by
  omega

/-- After the `p` and infinite local packet has been normalized to valuation
zero, the missing scalar is not a local Tamagawa statement: it is equality of
the Eisenstein exponent with the global isogeny-Selmer ratio. -/
theorem normalized_eisenstein_tamagawa_iff_selmer
    {eisensteinIndex selmerRatio awayTamagawa : ℤ}
    (hcassels : selmerRatio = awayTamagawa) :
    eisensteinIndex = awayTamagawa ↔ eisensteinIndex = selmerRatio := by
  simpa [hcassels]

/-- The Cassels ledger gives a finite falsifier: any discrepancy between the
Selmer-ratio side and `Eisenstein + local` disproves the proposed local scalar
identity. -/
theorem mismatch_blocks_eisenstein_tamagawa
    {eisensteinIndex selmerRatio localPacket awayTamagawa : ℤ}
    (hcassels : selmerRatio = localPacket + awayTamagawa)
    (hmismatch : selmerRatio ≠ eisensteinIndex + localPacket) :
    eisensteinIndex ≠ awayTamagawa := by
  intro heq
  apply hmismatch
  omega

/-- Source-blind local data cannot determine the away Tamagawa exponent.  Two
Cassels ledgers can have identical local packet and Eisenstein index but
opposite answers to the target equality because their global Selmer ratios
differ. -/
theorem same_local_data_different_global_outcome :
    ∃ eisensteinIndex localPacket
      selmerRatio₀ awayTamagawa₀ selmerRatio₁ awayTamagawa₁ : ℤ,
      selmerRatio₀ = localPacket + awayTamagawa₀ ∧
      selmerRatio₁ = localPacket + awayTamagawa₁ ∧
      eisensteinIndex = awayTamagawa₀ ∧
      eisensteinIndex ≠ awayTamagawa₁ := by
  exact ⟨0, 0, 0, 0, 1, 1, by norm_num, by norm_num, rfl, by norm_num⟩

/-- If a finite isogeny descent computes the Selmer-ratio exponent and the
normalized local packet, it computes the away Tamagawa exponent exactly. -/
theorem finite_descent_computes_away_tamagawa
    {phiSelmerDim dualSelmerDim localPacket awayTamagawa : ℤ}
    (hcassels : phiSelmerDim - dualSelmerDim =
      localPacket + awayTamagawa) :
    awayTamagawa =
      phiSelmerDim - dualSelmerDim - localPacket := by
  omega

/-- With local packet zero, a finite descent certificate for equality of the
Selmer dimensions difference and Eisenstein exponent closes the scalar row. -/
theorem normalized_scalar_closed_by_selmer_dimensions
    {phiSelmerDim dualSelmerDim eisensteinIndex awayTamagawa : ℤ}
    (hcassels : phiSelmerDim - dualSelmerDim = awayTamagawa)
    (hbalance : phiSelmerDim - dualSelmerDim = eisensteinIndex) :
    eisensteinIndex = awayTamagawa := by
  omega

#print axioms away_tamagawa_from_cassels
#print axioms eisenstein_tamagawa_iff_selmer_balance
#print axioms normalized_eisenstein_tamagawa_iff_selmer
#print axioms mismatch_blocks_eisenstein_tamagawa
#print axioms same_local_data_different_global_outcome
#print axioms finite_descent_computes_away_tamagawa
#print axioms normalized_scalar_closed_by_selmer_dimensions

end BSDIsogenySelmerRatioLedger
