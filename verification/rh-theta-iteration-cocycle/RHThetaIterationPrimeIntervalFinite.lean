import Mathlib

/-!
# RH theta-iteration prime-interval toll finite algebra

HONESTY BOUNDARY

This file verifies only the finite real algebra behind the paper-level
prime-interval form of the Chebyshev self-map cocycle. The variables `a,b`
stand for two square roots of consecutive states; `w` are nonnegative atom
weights; and `r` are reciprocal-root coordinates.

It does not formalize primes, the Chebyshev theta function, square-root
instantiation, interval membership, Stieltjes integration, Johnston's theorem,
zeta zeros, RH, or an official Clay statement.
-/

namespace MillenniumBraid
namespace RHThetaIterationPrimeIntervalFinite

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- The descending interval bracket is nonnegative when `0 < a`,
`0 ≤ b ≤ a`, and the reciprocal coordinate is at most `1/a`. -/
theorem descending_bracket_nonnegative
    {a b r : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hba : b ≤ a)
    (hr : r ≤ 1 / a) :
    0 ≤ 2 / (a + b) - r := by
  have hab : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
  have hfrac : (1 : ℝ) / a ≤ 2 / (a + b) := by
    apply (div_le_div_iff₀ ha hab).2
    nlinarith
  linarith

/-- The increasing interval bracket is nonnegative when `0 < a ≤ b`
and the reciprocal coordinate is at least `1/a`. -/
theorem increasing_bracket_nonnegative
    {a b r : ℝ}
    (ha : 0 < a)
    (hab : a ≤ b)
    (hr : 1 / a ≤ r) :
    0 ≤ r - 2 / (a + b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have habpos : 0 < a + b := add_pos ha hb
  have hfrac : 2 / (a + b) ≤ (1 : ℝ) / a := by
    apply (div_le_div_iff₀ habpos ha).2
    nlinarith
  linarith

/-- If the interval atom mass is `a²-b²`, rationalizing the two square-root
states gives the exact descending finite toll decomposition. -/
theorem descending_interval_toll_identity
    (s : Finset ι)
    (w r : ι → ℝ)
    (a b : ℝ)
    (hab : a + b ≠ 0)
    (hmass : ∑ i ∈ s, w i = a ^ 2 - b ^ 2) :
    2 * (a - b) - ∑ i ∈ s, w i * r i =
      ∑ i ∈ s, w i * (2 / (a + b) - r i) := by
  calc
    2 * (a - b) - ∑ i ∈ s, w i * r i =
        (2 / (a + b)) * (∑ i ∈ s, w i) -
          ∑ i ∈ s, w i * r i := by
            rw [hmass]
            field_simp [hab]
            ring
    _ = ∑ i ∈ s, w i * (2 / (a + b) - r i) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      ring

/-- If the interval atom mass is `b²-a²`, rationalizing the two square-root
states gives the exact increasing finite toll decomposition. -/
theorem increasing_interval_toll_identity
    (s : Finset ι)
    (w r : ι → ℝ)
    (a b : ℝ)
    (hab : a + b ≠ 0)
    (hmass : ∑ i ∈ s, w i = b ^ 2 - a ^ 2) :
    (∑ i ∈ s, w i * r i) - 2 * (b - a) =
      ∑ i ∈ s, w i * (r i - 2 / (a + b)) := by
  calc
    (∑ i ∈ s, w i * r i) - 2 * (b - a) =
        (∑ i ∈ s, w i * r i) -
          (2 / (a + b)) * (∑ i ∈ s, w i) := by
            rw [hmass]
            field_simp [hab]
            ring
    _ = ∑ i ∈ s, w i * (r i - 2 / (a + b)) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      ring

/-- Nonnegative weights and descending reciprocal ordering make the complete
finite interval toll nonnegative. -/
theorem descending_interval_toll_nonnegative
    (s : Finset ι)
    (w r : ι → ℝ)
    {a b : ℝ}
    (ha : 0 < a)
    (hb : 0 ≤ b)
    (hba : b ≤ a)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hr : ∀ i ∈ s, r i ≤ 1 / a) :
    0 ≤ ∑ i ∈ s, w i * (2 / (a + b) - r i) := by
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw i hi)
      (descending_bracket_nonnegative ha hb hba (hr i hi))

/-- Nonnegative weights and increasing reciprocal ordering make the complete
finite interval toll nonnegative. -/
theorem increasing_interval_toll_nonnegative
    (s : Finset ι)
    (w r : ι → ℝ)
    {a b : ℝ}
    (ha : 0 < a)
    (hab : a ≤ b)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hr : ∀ i ∈ s, 1 / a ≤ r i) :
    0 ≤ ∑ i ∈ s, w i * (r i - 2 / (a + b)) := by
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw i hi)
      (increasing_bracket_nonnegative ha hab (hr i hi))

#print axioms descending_bracket_nonnegative
#print axioms increasing_bracket_nonnegative
#print axioms descending_interval_toll_identity
#print axioms increasing_interval_toll_identity
#print axioms descending_interval_toll_nonnegative
#print axioms increasing_interval_toll_nonnegative

end RHThetaIterationPrimeIntervalFinite
end MillenniumBraid
