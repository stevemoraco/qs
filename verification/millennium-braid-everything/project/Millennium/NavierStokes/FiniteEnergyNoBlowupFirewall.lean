import Mathlib

/-!
# Finite-energy no-blowup firewall

This file isolates a necessary obstruction for every finite-mode Navier--Stokes
or Euler cascade model.  A uniform bound on the sum of squared amplitudes
bounds every individual amplitude, so no fixed finite-dimensional truncation
can exhibit coordinate blow-up.  Any singularity mechanism must therefore
cross an explicitly infinite-dimensional limit (or abandon the energy bound).

This is finite real algebra only.  It is not a Navier--Stokes solution.
-/

namespace Millennium.NavierStokes

open Finset

/-- One squared coordinate is bounded by the total sum of squares. -/
theorem coordinateSq_le_totalSq
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) :
    (x i) ^ 2 ≤ ∑ j : ι, (x j) ^ 2 := by
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

/-- A uniform finite-energy bound controls every coordinate at every time. -/
theorem coordinateSq_le_energy
    {τ ι : Type*} [Fintype ι]
    (x : τ → ι → ℝ) (E : ℝ)
    (henergy : ∀ t, (∑ j : ι, (x t j) ^ 2) ≤ E) :
    ∀ t i, (x t i) ^ 2 ≤ E := by
  intro t i
  exact (coordinateSq_le_totalSq (x t) i).trans (henergy t)

/-- No coordinate can be unbounded in square while total finite-mode energy is
uniformly bounded.  This is the exact quantifier firewall needed before a
finite rotor or Galerkin gadget is promoted to an infinite cascade. -/
theorem noCoordinateSqUnbounded_of_energyBound
    {τ ι : Type*} [Fintype ι]
    (x : τ → ι → ℝ) (E : ℝ)
    (henergy : ∀ t, (∑ j : ι, (x t j) ^ 2) ≤ E) :
    ¬ ∃ i : ι, ∀ M : ℝ, ∃ t : τ, M < (x t i) ^ 2 := by
  rintro ⟨i, hi⟩
  obtain ⟨t, ht⟩ := hi E
  have hle : (x t i) ^ 2 ≤ E := coordinateSq_le_energy x E henergy t i
  linarith

/-- Exact conservation is a special case of the uniform energy-bound firewall. -/
theorem noCoordinateSqUnbounded_of_energyConservation
    {τ ι : Type*} [Fintype ι]
    (x : τ → ι → ℝ) (E : ℝ)
    (henergy : ∀ t, (∑ j : ι, (x t j) ^ 2) = E) :
    ¬ ∃ i : ι, ∀ M : ℝ, ∃ t : τ, M < (x t i) ^ 2 := by
  apply noCoordinateSqUnbounded_of_energyBound x E
  intro t
  exact (henergy t).le

#print axioms coordinateSq_le_totalSq
#print axioms coordinateSq_le_energy
#print axioms noCoordinateSqUnbounded_of_energyBound
#print axioms noCoordinateSqUnbounded_of_energyConservation

end Millennium.NavierStokes
