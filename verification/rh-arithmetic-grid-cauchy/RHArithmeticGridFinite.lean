import Mathlib

/-!
# RH arithmetic-grid Cauchy finite firewalls

This file formalizes only elementary scalar pieces used in the arithmetic-grid
Cauchy Toeplitz theorem and its perturbation/certificate audit.

It does not formalize Hardy exponentials, Gram matrices, Toeplitz symbols,
Fejer kernels, the Cauchy determinant, Euler products, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHArithmeticGridFinite

/-- The denominator comparison behind the bounded-displacement perturbation
estimate.  For a grid distance `d ≥ 1`, moving each endpoint by at most `η`
loses at most the factor `1-2η`. -/
theorem displacement_denominator
    (d η : ℝ)
    (hd : 1 ≤ d)
    (hη : 0 ≤ η) :
    (1 - 2 * η) * d ≤ d - 2 * η := by
  nlinarith [mul_nonneg hη (sub_nonneg.mpr hd)]

/-- Polynomialized entry-error upgrade from the exact displaced denominator to
the simpler `d²` majorant used in the Schur sum. -/
theorem polynomialized_entry_error
    (E r η d : ℝ)
    (hE : 0 ≤ E)
    (_hr : 0 ≤ r)
    (hη : 0 ≤ η)
    (hd : 1 ≤ d)
    (hexact : E * (d * (d - 2 * η)) ≤ 4 * r * η) :
    E * ((1 - 2 * η) * d ^ 2) ≤ 4 * r * η := by
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have hden := displacement_denominator d η hd hη
  have hleft :
      (E * d) * ((1 - 2 * η) * d) ≤ (E * d) * (d - 2 * η) :=
    mul_le_mul_of_nonneg_left hden (mul_nonneg hE hd0)
  have hcompare :
      E * ((1 - 2 * η) * d ^ 2) ≤ E * (d * (d - 2 * η)) := by
    calc
      E * ((1 - 2 * η) * d ^ 2)
          = (E * d) * ((1 - 2 * η) * d) := by ring
      _ ≤ (E * d) * (d - 2 * η) := hleft
      _ = E * (d * (d - 2 * η)) := by ring
  exact hcompare.trans hexact

/-- Scalar Weyl-budget shadow: a base floor `A` and perturbation norm `δ`
give the repaired floor `A-δ`. -/
theorem perturbation_floor_budget
    (A δ lam : ℝ)
    (hlam : A - δ ≤ lam) :
    0 < A - δ → 0 < lam := by
  intro hpos
  linarith

/-- Once a certified lower bound for the absolute-coherence radius reaches one,
the fusion-frame hypothesis `ρ<1` is impossible. -/
theorem scalar_fusion_certificate_fails
    (ρ lower : ℝ)
    (hone : 1 ≤ lower)
    (hlower : lower ≤ ρ) :
    ¬ ρ < 1 := by
  linarith

/-- Every nontrivial Cauchy determinant pair factor lies strictly between zero
and one. -/
theorem determinant_pair_factor_strict
    (r d : ℝ)
    (hr : 0 < r)
    (hd : 0 < d) :
    0 < d ^ 2 / (d ^ 2 + 4 * r ^ 2) ∧
      d ^ 2 / (d ^ 2 + 4 * r ^ 2) < 1 := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hden : 0 < d ^ 2 + 4 * r ^ 2 := by positivity
  constructor
  · exact div_pos hd2 hden
  · exact (div_lt_one hden).2 (by nlinarith)

/-- A fixed positive floor can coexist with an exponentially small product:
this scalar family is the finite logical shadow of the determinant firewall. -/
theorem fixed_floor_exponential_product (n : ℕ) :
    0 < (1 / 2 : ℝ) ^ n ∧ (1 / 2 : ℝ) ≤ 1 := by
  constructor
  · positivity
  · norm_num

#print axioms displacement_denominator
#print axioms polynomialized_entry_error
#print axioms perturbation_floor_budget
#print axioms scalar_fusion_certificate_fails
#print axioms determinant_pair_factor_strict
#print axioms fixed_floor_exponential_product

end RHArithmeticGridFinite
end MillenniumBraid
