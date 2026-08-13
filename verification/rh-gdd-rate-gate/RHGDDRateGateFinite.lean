import Mathlib

/-!
# RH GDD literature-transfer rate-gate finite firewalls

HONESTY BOUNDARY

This file verifies only two finite/scalar facts used in a source audit:

* if `M` color classes each contain at most `B` objects, their total count is
  at most `M * B`;
* a strictly positive floor at every finite complexity may still decay exactly
  exponentially in a cofinal height parameter.

It does not formalize separated sequences, zeta zeros, the Riemann--von
Mangoldt formula, generalized divided differences, Riesz bases, Hardy spaces,
Avdonin--Ivanov, or RH.
-/

namespace MillenniumBraid
namespace RHGDDRateGateFinite

/-- Finite counting core of the density obstruction: a fixed number of color
classes, each with a fixed capacity, has only linear total capacity. -/
theorem colored_capacity_bound
    (M B : ℕ)
    (count : Fin M → ℕ)
    (hcount : ∀ color, count color ≤ B) :
    (∑ color, count color) ≤ M * B := by
  calc
    (∑ color, count color) ≤ ∑ _color : Fin M, B := by
      apply Finset.sum_le_sum
      intro color _hcolor
      exact hcount color
    _ = M * B := by simp

/-- Finite pigeonhole-style contrapositive. -/
theorem some_color_exceeds_capacity
    (M B : ℕ)
    (count : Fin M → ℕ)
    (htotal : M * B < ∑ color, count color) :
    ∃ color, B < count color := by
  by_contra hnone
  push_neg at hnone
  have hbound := colored_capacity_bound M B count hnone
  omega

/-- Cofinal height scale used in the qualitative-rate countermodel. -/
def height (n : ℕ) : ℕ := 2 ^ n

/-- A positive floor for every finite complexity whose binary logarithmic loss
is exactly the height `2^n`. -/
def qualitativeFloor (n : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ height n

/-- Every finite-complexity floor in the countermodel is strictly positive. -/
theorem qualitativeFloor_pos (n : ℕ) :
    0 < qualitativeFloor n := by
  unfold qualitativeFloor
  positivity

/-- Exact exponential-scale identity:
`2^(height n) * qualitativeFloor n = 1`. -/
theorem qualitativeFloor_exact_exponential_scale (n : ℕ) :
    (2 : ℚ) ^ height n * qualitativeFloor n = 1 := by
  unfold qualitativeFloor
  rw [← mul_pow]
  norm_num

/-- The height scale dominates `n+1`. -/
theorem height_ge_succ (n : ℕ) :
    n + 1 ≤ height n := by
  unfold height
  exact Nat.succ_le_two_pow n

/-- Pointwise positivity supplies no quantitative rate beyond positivity. -/
theorem pointwise_positive_stays_pointwise
    (A : ℕ → ℚ)
    (hA : ∀ n, 0 < A n) :
    ∀ n, 0 < A n := hA

#print axioms colored_capacity_bound
#print axioms some_color_exceeds_capacity
#print axioms qualitativeFloor_pos
#print axioms qualitativeFloor_exact_exponential_scale
#print axioms height_ge_succ
#print axioms pointwise_positive_stays_pointwise

end RHGDDRateGateFinite
end MillenniumBraid
