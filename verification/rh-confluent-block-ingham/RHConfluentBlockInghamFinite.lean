import Mathlib

/-!
# RH confluent block Ingham finite firewalls

This file verifies only finite scalar and polynomial-algebra shadows used by an
explicit lower-frame theorem for separated carrier frequencies with exact
multiplicity blocks.

It does not formalize the Montgomery--Vaughan Hilbert inequality, Legendre
polynomials, polynomial trace or inverse inequalities, integration by parts,
Tonelli/layer-cake, Hardy spaces, zeta zeros, or RH.
-/

namespace MillenniumBraid
namespace RHConfluentBlockInghamFinite

/-- If a finite-time lower estimate has defect `L/T`, then choosing
`T ≥ 2L` leaves at least one half of the diagonal energy. -/
theorem threshold_leaves_half
    (L T I D : ℝ)
    (hL : 0 < L)
    (hT : 2 * L ≤ T)
    (hD : 0 ≤ D)
    (hI : (1 - L / T) * D ≤ I) :
    (1 / 2 : ℝ) * D ≤ I := by
  have hTpos : 0 < T := by nlinarith
  have hratio : L / T ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hTpos).2
    nlinarith
  nlinarith

/-- The local Pascal Gram of a multiplicity-two block dominates `1/5 I`. -/
theorem pascal_two_floor (x₀ x₁ : ℝ) :
    (1 : ℝ) * x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₁ ^ 2 ≥
      (1 / 5 : ℝ) * (x₀ ^ 2 + x₁ ^ 2) := by
  have hid :
      ((1 : ℝ) * x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₁ ^ 2) -
          (1 / 5 : ℝ) * (x₀ ^ 2 + x₁ ^ 2) =
        (4 / 5 : ℝ) * (x₀ + (5 / 4 : ℝ) * x₁) ^ 2 +
          (11 / 20 : ℝ) * x₁ ^ 2 := by
    ring
  have hnonneg :
      0 ≤ (4 / 5 : ℝ) * (x₀ + (5 / 4 : ℝ) * x₁) ^ 2 +
          (11 / 20 : ℝ) * x₁ ^ 2 := by
    positivity
  nlinarith [hid, hnonneg]

/-- The local Pascal Gram of a multiplicity-three block dominates `1/21 I`. -/
theorem pascal_three_floor (x₀ x₁ x₂ : ℝ) :
    x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₀ * x₂ +
        2 * x₁ ^ 2 + 6 * x₁ * x₂ + 6 * x₂ ^ 2 ≥
      (1 / 21 : ℝ) * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) := by
  have hid :
      (x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₀ * x₂ +
          2 * x₁ ^ 2 + 6 * x₁ * x₂ + 6 * x₂ ^ 2) -
          (1 / 21 : ℝ) * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) =
        (20 / 21 : ℝ) *
            (x₀ + (21 / 20 : ℝ) * x₁ + (21 / 20 : ℝ) * x₂) ^ 2 +
          (379 / 420 : ℝ) *
            (x₁ + (819 / 379 : ℝ) * x₂) ^ 2 +
          (5480 / 7959 : ℝ) * x₂ ^ 2 := by
    ring
  have hnonneg :
      0 ≤ (20 / 21 : ℝ) *
            (x₀ + (21 / 20 : ℝ) * x₁ + (21 / 20 : ℝ) * x₂) ^ 2 +
          (379 / 420 : ℝ) *
            (x₁ + (819 / 379 : ℝ) * x₂) ^ 2 +
          (5480 / 7959 : ℝ) * x₂ ^ 2 := by
    positivity
  nlinarith [hid, hnonneg]

/-- The local Pascal Gram of a multiplicity-four block dominates `1/85 I`. -/
theorem pascal_four_floor (x₀ x₁ x₂ x₃ : ℝ) :
    x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₀ * x₂ + 2 * x₀ * x₃ +
        2 * x₁ ^ 2 + 6 * x₁ * x₂ + 8 * x₁ * x₃ +
        6 * x₂ ^ 2 + 20 * x₂ * x₃ + 20 * x₃ ^ 2 ≥
      (1 / 85 : ℝ) * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by
  have hid :
      (x₀ ^ 2 + 2 * x₀ * x₁ + 2 * x₀ * x₂ + 2 * x₀ * x₃ +
          2 * x₁ ^ 2 + 6 * x₁ * x₂ + 8 * x₁ * x₃ +
          6 * x₂ ^ 2 + 20 * x₂ * x₃ + 20 * x₃ ^ 2) -
          (1 / 85 : ℝ) * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) =
        (84 / 85 : ℝ) *
            (x₀ + (85 / 84 : ℝ) * x₁ + (85 / 84 : ℝ) * x₂ +
              (85 / 84 : ℝ) * x₃) ^ 2 +
          (6971 / 7140 : ℝ) *
            (x₁ + (14195 / 6971 : ℝ) * x₂ +
              (21335 / 6971 : ℝ) * x₃) ^ 2 +
          (549864 / 592535 : ℝ) *
            (x₂ + (215050 / 68733 : ℝ) * x₃) ^ 2 +
          (4363592 / 5842305 : ℝ) * x₃ ^ 2 := by
    ring
  have hnonneg :
      0 ≤ (84 / 85 : ℝ) *
            (x₀ + (85 / 84 : ℝ) * x₁ + (85 / 84 : ℝ) * x₂ +
              (85 / 84 : ℝ) * x₃) ^ 2 +
          (6971 / 7140 : ℝ) *
            (x₁ + (14195 / 6971 : ℝ) * x₂ +
              (21335 / 6971 : ℝ) * x₃) ^ 2 +
          (549864 / 592535 : ℝ) *
            (x₂ + (215050 / 68733 : ℝ) * x₃) ^ 2 +
          (4363592 / 5842305 : ℝ) * x₃ ^ 2 := by
    positivity
  nlinarith [hid, hnonneg]

/-- The transparent block coefficient is strictly positive whenever the
analytic shape and local floor are positive. -/
theorem positive_block_floor
    (localFloor exponent : ℝ)
    (hlocal : 0 < localFloor) :
    0 < (1 / 2 : ℝ) * Real.exp (-exponent) * localFloor := by
  positivity

/-- A vanishing minimum spacing can make the explicit exponential debt
arbitrarily large; finite positivity alone does not provide uniformity. -/
theorem inverse_spacing_debt_monotone
    (a K h₁ h₂ : ℝ)
    (ha : 0 ≤ a)
    (hK : 0 ≤ K)
    (hh₁ : 0 < h₁)
    (_hh₂ : 0 < h₂)
    (hle : h₁ ≤ h₂) :
    a * K / h₂ ≤ a * K / h₁ := by
  have hnum : 0 ≤ a * K := mul_nonneg ha hK
  exact div_le_div_of_nonneg_left hnum hh₁ hle

#print axioms threshold_leaves_half
#print axioms pascal_two_floor
#print axioms pascal_three_floor
#print axioms pascal_four_floor
#print axioms positive_block_floor
#print axioms inverse_spacing_debt_monotone

end RHConfluentBlockInghamFinite
end MillenniumBraid
