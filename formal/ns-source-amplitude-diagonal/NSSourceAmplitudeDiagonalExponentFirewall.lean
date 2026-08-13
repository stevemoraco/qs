namespace NavierStokesSourceAmplitudeDiagonal

/--
The canonical rational amplitude witness is `a = 4/3`.  We keep the
calculation denominator-free: all exponent signs are decided after
multiplication by the positive denominator `3`.
-/
def amplitudeNumerator : Nat := 4

def amplitudeDenominator : Nat := 3

/-- `5/4 < 4/3 < 3/2`, written by positive cross multiplication. -/
theorem witness_in_open_window :
    5 * amplitudeDenominator < 4 * amplitudeNumerator ∧
    2 * amplitudeNumerator < 3 * amplitudeDenominator := by
  decide

/--
For `a = 4/3`, the quadratic Xi energy/dissipation exponent
`3 - 2a` equals `1/3`.
-/
theorem xi_decay_exponent :
    3 * amplitudeDenominator =
      2 * amplitudeNumerator + 1 := by
  rfl

/--
The source square-density and critical-Hilbert battery exponent
`7 - 4a` equals `5/3`.
-/
theorem source_density_decay_exponent :
    7 * amplitudeDenominator =
      4 * amplitudeNumerator + 5 := by
  rfl

/--
The squared L1 source-battery exponent `8 - 4a` equals `8/3`.
-/
theorem source_l1_battery_decay_exponent :
    8 * amplitudeDenominator =
      4 * amplitudeNumerator + 8 := by
  rfl

/--
The endpoint source-gradient exponent `5 - 4a` equals `-1/3`;
equivalently `4a - 5 = 1/3`, so the declared source H1 energy diverges.
-/
theorem endpoint_source_gradient_divergence_exponent :
    4 * amplitudeNumerator =
      5 * amplitudeDenominator + 1 := by
  rfl

/-- All four strict sign conditions hold simultaneously at `a = 4/3`. -/
theorem vanishing_ledger_divergent_endpoint_firewall :
    5 * amplitudeDenominator < 4 * amplitudeNumerator ∧
    2 * amplitudeNumerator < 3 * amplitudeDenominator ∧
    2 * amplitudeNumerator + 1 = 3 * amplitudeDenominator ∧
    4 * amplitudeNumerator + 5 = 7 * amplitudeDenominator ∧
    4 * amplitudeNumerator + 8 = 8 * amplitudeDenominator ∧
    5 * amplitudeDenominator + 1 = 4 * amplitudeNumerator := by
  decide

#print axioms witness_in_open_window
#print axioms xi_decay_exponent
#print axioms source_density_decay_exponent
#print axioms source_l1_battery_decay_exponent
#print axioms endpoint_source_gradient_divergence_exponent
#print axioms vanishing_ledger_divergent_endpoint_firewall

end NavierStokesSourceAmplitudeDiagonal
