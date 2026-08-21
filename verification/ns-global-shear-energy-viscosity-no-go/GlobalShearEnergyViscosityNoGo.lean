import Mathlib

namespace Millennium.NavierStokes.GlobalShearEnergyViscosityNoGo

open scoped BigOperators

 theorem finiteEnergy_forces_frequencyProductCeiling
    (E B C ν c S K : ℝ)
    (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (henergy : S * B ≤ E)
    (hamp : ν * c ^ 2 * K ≤ S * C) :
    ν * c ^ 2 * B * K ≤ E * C := by
  calc
    ν * c ^ 2 * B * K = (ν * c ^ 2 * K) * B := by ring
    _ ≤ (S * C) * B := mul_le_mul_of_nonneg_right hamp hB
    _ = (S * B) * C := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_right henergy hC

 theorem finiteEnergy_forces_frequencyCeiling
    (E B C ν c S K : ℝ)
    (hB : 0 < B)
    (hC : 0 ≤ C)
    (hν : 0 < ν)
    (hc : 0 < c)
    (henergy : S * B ≤ E)
    (hamp : ν * c ^ 2 * K ≤ S * C) :
    K ≤ E * C / (ν * c ^ 2 * B) := by
  have hden : 0 < ν * c ^ 2 * B := by positivity
  apply (le_div_iff₀ hden).2
  have hmain := finiteEnergy_forces_frequencyProductCeiling
    E B C ν c S K (le_of_lt hB) hC henergy hamp
  nlinarith [hmain]

 theorem noGlobalShearAmplifier_aboveFrequencyCeiling
    (E B C ν c K : ℝ)
    (hB : 0 < B)
    (hC : 0 ≤ C)
    (hν : 0 < ν)
    (hc : 0 < c)
    (hK : E * C / (ν * c ^ 2 * B) < K) :
    ¬ ∃ S : ℝ, S * B ≤ E ∧ ν * c ^ 2 * K ≤ S * C := by
  rintro ⟨S, henergy, hamp⟩
  have hle := finiteEnergy_forces_frequencyCeiling
    E B C ν c S K hB hC hν hc henergy hamp
  linarith

 theorem normalizedViscosity_lowerBound
    (ν K S Smax : ℝ)
    (hν : 0 ≤ ν)
    (hK : 0 ≤ K)
    (hS : 0 < S)
    (hSmax : S ≤ Smax) :
    ν * K / Smax ≤ ν * K / S := by
  have hnum : 0 ≤ ν * K := mul_nonneg hν hK
  exact div_le_div_of_nonneg_left hnum hS hSmax

#print axioms finiteEnergy_forces_frequencyProductCeiling
#print axioms finiteEnergy_forces_frequencyCeiling
#print axioms noGlobalShearAmplifier_aboveFrequencyCeiling
#print axioms normalizedViscosity_lowerBound

end Millennium.NavierStokes.GlobalShearEnergyViscosityNoGo
