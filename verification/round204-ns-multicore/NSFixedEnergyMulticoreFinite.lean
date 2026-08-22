import Mathlib

/-!
# Round 204 Navier--Stokes fixed-energy multicore scaling

This file formalizes only scalar scaling identities for disjoint rescaled
profiles. It does not construct a Navier--Stokes solution, a vorticity field,
a singularity, or prove/disprove the Clay problem.
-/

namespace Millennium
namespace Round204NavierStokes

/-- The energy proxy for `N` disjoint copies of amplitude `A` and radius `r`. -/
def multicoreEnergy (N A r : ℚ) : ℚ := N * A ^ 2 * r ^ 3

/-- The support-volume proxy for `N` disjoint radius-`r` copies. -/
def multicoreVolume (N r : ℚ) : ℚ := N * r ^ 3

/-- The vorticity-amplitude proxy scales as velocity amplitude divided by radius. -/
def vorticityAmplitude (A r : ℚ) : ℚ := A / r

/-- Choosing amplitude `N` and radius `1/N` leaves total energy exactly one. -/
theorem fixed_energy_many_core_identity
    (N : ℚ) (hN : N ≠ 0) :
    multicoreEnergy N N (1 / N) = 1 := by
  unfold multicoreEnergy
  field_simp [hN]

/-- Under the same scaling, the total support-volume proxy is `1/N^2`. -/
theorem shrinking_total_volume_identity
    (N : ℚ) (hN : N ≠ 0) :
    multicoreVolume N (1 / N) = 1 / N ^ 2 := by
  unfold multicoreVolume
  field_simp [hN]

/-- Under the same scaling, the vorticity-amplitude proxy is `N^2`. -/
theorem growing_vorticity_amplitude_identity
    (N : ℚ) (hN : N ≠ 0) :
    vorticityAmplitude N (1 / N) = N ^ 2 := by
  unfold vorticityAmplitude
  field_simp [hN]

/-- The three identities hold simultaneously. -/
theorem fixed_energy_multicore_scaling
    (N : ℚ) (hN : N ≠ 0) :
    multicoreEnergy N N (1 / N) = 1 ∧
    multicoreVolume N (1 / N) = 1 / N ^ 2 ∧
    vorticityAmplitude N (1 / N) = N ^ 2 := by
  exact ⟨fixed_energy_many_core_identity N hN,
    shrinking_total_volume_identity N hN,
    growing_vorticity_amplitude_identity N hN⟩

/-- Cubing the energy-only Chebyshev critical-tail upper bound exposes the
wrong extra factor of the threshold. -/
theorem energy_chebyshev_cube_has_extra_threshold
    (energy Lambda tail : ℝ)
    (hidentity : tail ^ 3 = energy / Lambda ^ 2)
    (hLambda : Lambda ≠ 0) :
    (Lambda * tail) ^ 3 = energy * Lambda := by
  calc
    (Lambda * tail) ^ 3 = Lambda ^ 3 * tail ^ 3 := by ring
    _ = Lambda ^ 3 * (energy / Lambda ^ 2) := by rw [hidentity]
    _ = energy * Lambda := by field_simp [hLambda]

#print axioms fixed_energy_many_core_identity
#print axioms shrinking_total_volume_identity
#print axioms growing_vorticity_amplitude_identity
#print axioms fixed_energy_multicore_scaling
#print axioms energy_chebyshev_cube_has_extra_threshold

end Round204NavierStokes
end Millennium
