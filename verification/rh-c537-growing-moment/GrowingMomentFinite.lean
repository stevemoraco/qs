import Mathlib

/-!
# Finite growing-moment / Gram core for RH C537

This file formalizes only finite algebraic shadows used by RH C537:

* the fixed-order strip-loss denominator `2(p+1)` and its first exact values;
* strict growth of that denominator with the moment order;
* nonnegativity of finite feature-Gram energies;
* nonnegativity of finite even-moment energies for signed marked coefficients.

It does not formalize primes, Chebyshev bounds, the square-root queue,
continuous integration, the persistence integral, tensor measures, BGST,
Suzuki/Landau, zeta zeros, or RH.
-/

namespace Millennium.RH.GrowingMomentFinite

open scoped BigOperators

/-- Denominator of the C537 subpower fixed-order strip loss `1 / (2(p+1))`. -/
def stripDenom (p : ℕ) : ℕ := 2 * (p + 1)

@[simp] theorem stripDenom_one : stripDenom 1 = 4 := by
  norm_num [stripDenom]

@[simp] theorem stripDenom_two : stripDenom 2 = 6 := by
  norm_num [stripDenom]

@[simp] theorem stripDenom_three : stripDenom 3 = 8 := by
  norm_num [stripDenom]

/-- Every fixed finite moment order leaves a strictly positive denominator. -/
theorem stripDenom_pos (p : ℕ) : 0 < stripDenom p := by
  unfold stripDenom
  omega

/-- Raising the moment order strictly increases the strip-loss denominator. -/
theorem stripDenom_succ_lt (p : ℕ) : stripDenom p < stripDenom (p + 1) := by
  unfold stripDenom
  omega

/-- At even moment order `p=2r`, the denominator is exactly `4r+2`. -/
theorem stripDenom_even (r : ℕ) : stripDenom (2 * r) = 4 * r + 2 := by
  unfold stripDenom
  omega

/-- A finite feature-map energy, i.e. a Gram quadratic written as a sum of squares. -/
noncomputable def featureEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (feature : ι → κ → ℝ) : ℝ :=
  ∑ k, (∑ i, a i * feature i k) ^ 2

/-- Finite feature-Gram energies are nonnegative even for signed marked coefficients. -/
theorem featureEnergy_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (feature : ι → κ → ℝ) :
    0 ≤ featureEnergy a feature := by
  unfold featureEnergy
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Finite even-moment energy of a marked feature sum. -/
noncomputable def evenMomentEnergy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℕ) (a : ι → ℝ) (feature : ι → κ → ℝ) : ℝ :=
  ∑ k, (∑ i, a i * feature i k) ^ (2 * r)

/-- Every finite even-moment energy is nonnegative. -/
theorem evenMomentEnergy_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ℕ) (a : ι → ℝ) (feature : ι → κ → ℝ) :
    0 ≤ evenMomentEnergy r a feature := by
  unfold evenMomentEnergy
  exact Finset.sum_nonneg fun _ _ => Even.pow_nonneg (even_two_mul r) _

#print axioms stripDenom_one
#print axioms stripDenom_two
#print axioms stripDenom_three
#print axioms stripDenom_pos
#print axioms stripDenom_succ_lt
#print axioms stripDenom_even
#print axioms featureEnergy_nonneg
#print axioms evenMomentEnergy_nonneg

end Millennium.RH.GrowingMomentFinite
