import Mathlib

/-!
# Finite algebra core for the BSD Bockstein defect-area identity

For an eventually constant defect profile `τ`, the torsion-length formula
reduces to a finite summation-by-parts identity.  This file isolates the
integer algebra independently of Selmer complexes.
-/

open scoped BigOperators

namespace BSDBraid

/--
Finite summation-by-parts identity underlying

  Σ i·(τ_{i-1}-τ_i) = Σ (τ_k-s).

With indices starting at zero, the weighted successive drops equal the
area under the profile, after subtracting the terminal rectangle.
-/
theorem weighted_drop_eq_area (τ : ℕ → ℤ) :
    ∀ n : ℕ,
      (∑ i in Finset.range n,
          ((i : ℤ) + 1) * (τ i - τ (i + 1))) =
        (∑ i in Finset.range n, τ i) - (n : ℤ) * τ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      ring

/--
If `τ n = s`, the weighted elementary-divisor multiplicities equal the
sum of the defects above the stable rank `s`.
-/
theorem weighted_drop_eq_defect_area
    (τ : ℕ → ℤ) (n : ℕ) (s : ℤ) (hstable : τ n = s) :
    (∑ i in Finset.range n,
        ((i : ℤ) + 1) * (τ i - τ (i + 1))) =
      ∑ i in Finset.range n, (τ i - s) := by
  rw [weighted_drop_eq_area τ n, hstable]
  rw [Finset.sum_sub_distrib]
  simp

end BSDBraid
