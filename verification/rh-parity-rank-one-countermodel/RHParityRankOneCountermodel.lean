import Mathlib

/-!
# Finite parity rank-one countermodel

This file gives an exact one-dimensional scalar countermodel to the inference

* pole-free even sector: a simple negative positive-generator direction;
* pole-free odd sector: positive;
* therefore the full odd sector lies above the full even sector.

The inference is false without controlling the signed rank-one pole updates.
For `Bₑ = -1`, `Bₒ = 1/2`, and pole coordinates `C = S = 1`, the updated
coefficients are `Aₑ = 1` and `Aₒ = -3/2`, so `Aₒ < Aₑ`.

Only finite scalar algebra is formalized.  Nothing here constructs a zeta
operator, identifies a Weil form, proves a parity theorem for such an operator,
or implies the Riemann hypothesis.
-/

namespace RHParityRankOneCountermodel

/-- A one-dimensional sector, represented by its single coordinate. -/
abbrev OneDimSector (𝕜 : Type*) := Fin 1 → 𝕜

/-- The distinguished positive coordinate direction. -/
def positiveGenerator {𝕜 : Type*} [One 𝕜] : OneDimSector 𝕜 := fun _ => 1

/-- Every vector in the sector is a scalar multiple of the distinguished
generator.  This is the exact finite-dimensional simplicity fact used here. -/
theorem oneDimSector_eq_smul_generator
    {𝕜 : Type*} [Semiring 𝕜] (x : OneDimSector 𝕜) :
    x = x 0 • positiveGenerator := by
  ext i
  fin_cases i
  simp [positiveGenerator]

/-- The distinguished generator is nonzero over a nontrivial semiring. -/
theorem positiveGenerator_ne_zero
    {𝕜 : Type*} [Semiring 𝕜] [Nontrivial 𝕜] :
    (positiveGenerator : OneDimSector 𝕜) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [positiveGenerator] using h0

/-- Scalar quadratic energy on a one-dimensional sector. -/
def scalarEnergy {𝕜 : Type*} [Ring 𝕜]
    (coefficient : 𝕜) (x : OneDimSector 𝕜) : 𝕜 :=
  coefficient * (x 0) ^ 2

/-- Even-sector rank-one update: the pole term has positive sign. -/
def evenFullEnergy {𝕜 : Type*} [Ring 𝕜]
    (Bₑ C : 𝕜) (x : OneDimSector 𝕜) : 𝕜 :=
  scalarEnergy Bₑ x + 2 * (C * x 0) ^ 2

/-- Odd-sector rank-one update: the pole term has negative sign. -/
def oddFullEnergy {𝕜 : Type*} [Ring 𝕜]
    (Bₒ S : 𝕜) (x : OneDimSector 𝕜) : 𝕜 :=
  scalarEnergy Bₒ x - 2 * (S * x 0) ^ 2

/-- The pole-free even coefficient `-1` has a positive, nonzero generator and
the entire eigendirection is one-dimensional.  The word "simple" here means
exactly the displayed spanning assertion; no infinite-dimensional spectral or
Perron--Frobenius theorem is imported. -/
theorem simpleNegativePositiveGeneratorCertificate
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    (positiveGenerator : OneDimSector 𝕜) ≠ 0 ∧
      (0 : 𝕜) < positiveGenerator 0 ∧
      scalarEnergy (-1 : 𝕜) positiveGenerator = -1 ∧
      (-1 : 𝕜) < 0 ∧
      ∀ x : OneDimSector 𝕜,
        ∃ a : 𝕜, x = a • positiveGenerator := by
  refine ⟨positiveGenerator_ne_zero, ?_, ?_, by norm_num, ?_⟩
  · simp [positiveGenerator]
  · norm_num [scalarEnergy, positiveGenerator]
  · intro x
    exact ⟨x 0, oneDimSector_eq_smul_generator x⟩

/-- Exact pole-free signs and full-energy order reversal.  This theorem is
uniform over every linear ordered field and therefore applies to both `ℚ` and
`ℝ`. -/
theorem parityRankOneOrderReversal
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    let Bₑ : 𝕜 := -1
    let Bₒ : 𝕜 := 1 / 2
    let C : 𝕜 := 1
    let S : 𝕜 := 1
    let Aₑ := Bₑ + 2 * C ^ 2
    let Aₒ := Bₒ - 2 * S ^ 2
    Bₑ < 0 ∧ 0 < Bₒ ∧ C = 1 ∧ S = 1 ∧
      Aₑ = 1 ∧ Aₒ = -3 / 2 ∧ Aₒ < Aₑ := by
  norm_num

/-- On the positive generators, the exact quadratic energies realize the same
order reversal: pole-free even is negative, pole-free odd is positive, but the
full odd energy is strictly below the full even energy. -/
theorem generatorEnergyOrderReversal
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    scalarEnergy (-1 : 𝕜) positiveGenerator = -1 ∧
      scalarEnergy (1 / 2 : 𝕜) positiveGenerator = 1 / 2 ∧
      evenFullEnergy (-1 : 𝕜) 1 positiveGenerator = 1 ∧
      oddFullEnergy (1 / 2 : 𝕜) 1 positiveGenerator = -3 / 2 ∧
      oddFullEnergy (1 / 2 : 𝕜) 1 positiveGenerator <
        evenFullEnergy (-1 : 𝕜) 1 positiveGenerator := by
  norm_num [scalarEnergy, evenFullEnergy, oddFullEnergy, positiveGenerator]

/-- Explicit rational instantiation of the abstract countermodel. -/
theorem rationalParityCountermodel :
    scalarEnergy (-1 : ℚ) positiveGenerator = -1 ∧
      scalarEnergy (1 / 2 : ℚ) positiveGenerator = 1 / 2 ∧
      evenFullEnergy (-1 : ℚ) 1 positiveGenerator = 1 ∧
      oddFullEnergy (1 / 2 : ℚ) 1 positiveGenerator = -3 / 2 ∧
      oddFullEnergy (1 / 2 : ℚ) 1 positiveGenerator <
        evenFullEnergy (-1 : ℚ) 1 positiveGenerator :=
  generatorEnergyOrderReversal

/-- Explicit real instantiation of the abstract countermodel. -/
theorem realParityCountermodel :
    scalarEnergy (-1 : ℝ) positiveGenerator = -1 ∧
      scalarEnergy (1 / 2 : ℝ) positiveGenerator = 1 / 2 ∧
      evenFullEnergy (-1 : ℝ) 1 positiveGenerator = 1 ∧
      oddFullEnergy (1 / 2 : ℝ) 1 positiveGenerator = -3 / 2 ∧
      oddFullEnergy (1 / 2 : ℝ) 1 positiveGenerator <
        evenFullEnergy (-1 : ℝ) 1 positiveGenerator :=
  generatorEnergyOrderReversal

#print axioms oneDimSector_eq_smul_generator
#print axioms positiveGenerator_ne_zero
#print axioms simpleNegativePositiveGeneratorCertificate
#print axioms parityRankOneOrderReversal
#print axioms generatorEnergyOrderReversal
#print axioms rationalParityCountermodel
#print axioms realParityCountermodel

end RHParityRankOneCountermodel
