import Mathlib

/-!
# RH admissible-window localization: finite algebra core

Honesty status: this file formalizes only two finite pieces of the Run 24
analytic proof:

* iteration of a reverse-doubling inequality along a finite dyadic chain;
* the product bound obtained when `N` Fourier factors each have modulus at most
  one half.

It does not define the zeta function, the Weil distribution, the triangular
box family, compact measures, infinite products, Fourier transforms, improper
integrals, admissible windows, or RH. A clean build verifies only the displayed
finite implications.
-/

namespace MillenniumBraid
namespace RHAdmissibleWindowFinite

/-- Finite iteration of a reverse-doubling lower growth estimate. -/
theorem reverseDoublingIterate
    (R : ℕ → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (hstep : ∀ n : ℕ, κ * R n ≤ R (n + 1)) :
    ∀ m : ℕ, κ ^ m * R 0 ≤ R m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        κ ^ (m + 1) * R 0 = κ * (κ ^ m * R 0) := by ring
        _ ≤ κ * R m := mul_le_mul_of_nonneg_left ih hκ
        _ ≤ R (m + 1) := hstep m

/-- Division form used when the dyadic chain is read backwards. -/
theorem reverseDoublingDivision
    (R : ℕ → ℝ) (κ : ℝ)
    (hκ : 0 < κ)
    (hstep : ∀ n : ℕ, κ * R n ≤ R (n + 1))
    (m : ℕ) :
    R 0 ≤ R m / κ ^ m := by
  apply (le_div_iff₀ (pow_pos hκ m)).2
  simpa [mul_comm] using reverseDoublingIterate R κ (le_of_lt hκ) hstep m

/--
A finite block of factors, each bounded in modulus by one half, contributes an
exponential product loss `2^{-N}`.
-/
theorem listAbsProdLeHalfPow
    (xs : List ℝ)
    (hhalf : ∀ x ∈ xs, |x| ≤ (1 / 2 : ℝ)) :
    |xs.prod| ≤ (1 / 2 : ℝ) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : |x| ≤ (1 / 2 : ℝ) := hhalf x (by simp)
      have htail : ∀ y ∈ xs, |y| ≤ (1 / 2 : ℝ) := by
        intro y hy
        exact hhalf y (by simp [hy])
      have hi := ih htail
      have hnonnegProd : 0 ≤ |xs.prod| := abs_nonneg _
      have hnonnegHalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have hmul : |x| * |xs.prod| ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ xs.length) :=
        mul_le_mul hx hi hnonnegProd hnonnegHalf
      simpa [List.prod_cons, abs_mul, pow_succ, mul_comm, mul_left_comm,
        mul_assoc] using hmul

/-- Cardinality-specialized version for exactly `N` factors. -/
theorem finAbsProdLeHalfPow
    (N : ℕ) (f : Fin N → ℝ)
    (hhalf : ∀ i, |f i| ≤ (1 / 2 : ℝ)) :
    |(List.ofFn f).prod| ≤ (1 / 2 : ℝ) ^ N := by
  apply listAbsProdLeHalfPow
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hhalf i

/-- Squaring the factor bound produces the `4^{-N}` probability-tail budget. -/
theorem squareFactorBudget
    (N : ℕ) (p : ℝ)
    (hp : |p| ≤ (1 / 2 : ℝ) ^ N) :
    p ^ 2 ≤ (1 / 4 : ℝ) ^ N := by
  have habsnonneg : 0 ≤ |p| := abs_nonneg _
  have hpowNonneg : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  have hsquare := mul_le_mul hp hp habsnonneg hpowNonneg
  simpa [pow_two, abs_mul_self, ← pow_mul] using hsquare

#print axioms reverseDoublingIterate
#print axioms reverseDoublingDivision
#print axioms listAbsProdLeHalfPow
#print axioms finAbsProdLeHalfPow
#print axioms squareFactorBudget

end RHAdmissibleWindowFinite
end MillenniumBraid
