namespace NavierStokesSourceDualAxisTrace

/--
A finite logarithmic-annulus plateau. `annuli` records the number of unit
logarithmic cells on which the profile is identically one. The continuum
profile has exactly two transition layers, one at each end of the plateau.
-/
structure TwoJumpPlateau where
  annuli : Nat

/-- Discrete shadow of the critical trace mass `∫ |φ|² dr/r`. -/
def traceMass (p : TwoJumpPlateau) : Nat := p.annuli

/-- Discrete shadow of the radial energy `∫ r |∂ᵣ φ|² dr`.
The logarithmic plateau has exactly two unit transition layers. -/
def jumpEnergy (_p : TwoJumpPlateau) : Nat := 2

/-- The canonical plateau occupying `N` logarithmic annuli. -/
def plateau (N : Nat) : TwoJumpPlateau := ⟨N⟩

/-- Exact finite values behind the logarithmic-annulus trace obstruction. -/
theorem plateau_values (N : Nat) :
    traceMass (plateau N) = N ∧ jumpEnergy (plateau N) = 2 := by
  exact ⟨rfl, rfl⟩

/--
No uniform multiplicative bound can control the trace mass by the two-jump
energy in this finite model: for every proposed constant `C`, one can choose a
long enough plateau so that `C * energy < trace`.
-/
theorem no_uniform_trace_bound (C : Nat) :
    ∃ p : TwoJumpPlateau, C * jumpEnergy p < traceMass p := by
  refine ⟨plateau (Nat.succ (C * 2)), ?_⟩
  change C * 2 < Nat.succ (C * 2)
  exact Nat.lt_succ_self (C * 2)

/-- The trace mass is unbounded while the transition energy stays exactly two. -/
theorem arbitrarily_large_trace_at_fixed_energy (B : Nat) :
    ∃ p : TwoJumpPlateau, B < traceMass p ∧ jumpEnergy p = 2 := by
  refine ⟨plateau (Nat.succ B), ?_, rfl⟩
  exact Nat.lt_succ_self B

#print axioms plateau_values
#print axioms no_uniform_trace_bound
#print axioms arbitrarily_large_trace_at_fixed_energy

end NavierStokesSourceDualAxisTrace
