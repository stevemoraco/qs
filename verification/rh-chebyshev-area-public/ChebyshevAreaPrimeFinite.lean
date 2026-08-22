import Mathlib

/-!
# Genuine finite-prime geometry of Johnston's Chebyshev-area criterion

This file replaces the arbitrary weighted support by the actual finite prime
weights `log p`. At prefix `n`, define

`thetaNat n = sum over p ≤ n of (p.Prime ? log p : 0)`

and the corresponding closed-form area parabola

`primeArea n x = x^2 / 2 - 2 - sum over p ≤ n of (x-p) log p`.

On the real unit interval `[n,n+1]`, this is exactly the integrated Chebyshev
staircase, up to the separate analytic theorem identifying the real integral
with the finite sum. The file proves the prefix recurrences, the exact
parabola, endpoint compatibility, and equivalence between positivity on each
unit interval and positivity of one explicit interval minimum.

It does not define the infinite real Chebyshev function, prove the interval
integral identity, prove Johnston's analytic equivalence, or prove the minimum
positive.
-/

namespace Millennium.RH.ChebyshevAreaPrimeFinite

open Set

noncomputable section

/-- The actual logarithmic prime weight, zero on composite indices. -/
def primeWeight (p : ℕ) : ℝ :=
  if Nat.Prime p then Real.log p else 0

/-- Finite Chebyshev prefix `sum_{p≤n} log p`. -/
def thetaNat (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum primeWeight

/-- Finite first prime moment `sum_{p≤n} p log p`. -/
def primeMoment (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun p => (p : ℝ) * primeWeight p)

/-- Closed-form area on a unit interval carrying the prime prefix through `n`. -/
def primeArea (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 / 2 - 2 -
    (Finset.range (n + 1)).sum
      (fun p => (x - (p : ℝ)) * primeWeight p)

/-- Value of the prime-prefix area parabola at its center. -/
def primeCenter (n : ℕ) : ℝ :=
  primeMoment n - thetaNat n ^ 2 / 2 - 2

/-- Adding one integer index adds exactly its prime weight. -/
theorem thetaNat_succ (n : ℕ) :
    thetaNat (n + 1) = thetaNat n + primeWeight (n + 1) := by
  unfold thetaNat
  rw [Finset.sum_range_succ]

/-- The first prime moment has the corresponding exact prefix recurrence. -/
theorem primeMoment_succ (n : ℕ) :
    primeMoment (n + 1) =
      primeMoment n + (n + 1 : ℝ) * primeWeight (n + 1) := by
  unfold primeMoment
  rw [Finset.sum_range_succ]
  push_cast
  rfl

/-- Exact update of the finite area after adding the next possible prime. -/
theorem primeArea_succ (n : ℕ) (x : ℝ) :
    primeArea (n + 1) x =
      primeArea n x - (x - (n + 1 : ℝ)) * primeWeight (n + 1) := by
  unfold primeArea
  rw [Finset.sum_range_succ]
  push_cast
  ring

/-- At the new integer endpoint, the newly added prime term has zero lever arm. -/
theorem primeArea_endpoint_compatible (n : ℕ) :
    primeArea (n + 1) (n + 1 : ℝ) =
      primeArea n (n + 1 : ℝ) := by
  rw [primeArea_succ]
  ring

/-- Exact prime-prefix parabola identity. -/
theorem primeArea_eq_center_add_square (n : ℕ) (x : ℝ) :
    primeArea n x =
      primeCenter n + (x - thetaNat n) ^ 2 / 2 := by
  unfold primeArea primeCenter primeMoment thetaNat
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The center is the global minimum of the prefix parabola. -/
theorem primeCenter_le_primeArea (n : ℕ) (x : ℝ) :
    primeCenter n ≤ primeArea n x := by
  rw [primeArea_eq_center_add_square]
  nlinarith [sq_nonneg (x - thetaNat n)]

/-- Exact minimum value of the prefix parabola on the unit interval `[n,n+1]`. -/
def unitIntervalMinimum (n : ℕ) : ℝ :=
  if thetaNat n ≤ (n : ℝ) then
    primeArea n n
  else if thetaNat n ≤ (n + 1 : ℝ) then
    primeCenter n
  else
    primeArea n (n + 1 : ℝ)

/-- The explicit interval minimum is below every area value in its unit interval. -/
theorem unitIntervalMinimum_le_primeArea
    (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (n : ℝ) (n + 1 : ℝ)) :
    unitIntervalMinimum n ≤ primeArea n x := by
  unfold unitIntervalMinimum
  by_cases hleft : thetaNat n ≤ (n : ℝ)
  · simp only [hleft, if_true]
    have hstep :
        0 ≤ (x - thetaNat n) - ((n : ℝ) - thetaNat n) := by
      linarith [hx.1]
    have hsum :
        0 ≤ (x - thetaNat n) + ((n : ℝ) - thetaNat n) := by
      linarith [hx.1, hleft]
    have hprod :
        0 ≤
          ((x - thetaNat n) - ((n : ℝ) - thetaNat n)) *
          ((x - thetaNat n) + ((n : ℝ) - thetaNat n)) :=
      mul_nonneg hstep hsum
    rw [primeArea_eq_center_add_square, primeArea_eq_center_add_square]
    nlinarith
  · simp only [hleft, if_false]
    by_cases hright : thetaNat n ≤ (n + 1 : ℝ)
    · simp only [hright, if_true]
      exact primeCenter_le_primeArea n x
    · simp only [hright, if_false]
      have hright' : (n + 1 : ℝ) ≤ thetaNat n := le_of_not_ge hright
      have hstep :
          0 ≤ (thetaNat n - x) - (thetaNat n - (n + 1 : ℝ)) := by
        linarith [hx.2]
      have hsum :
          0 ≤ (thetaNat n - x) + (thetaNat n - (n + 1 : ℝ)) := by
        linarith [hx.2, hright']
      have hprod :
          0 ≤
            ((thetaNat n - x) - (thetaNat n - (n + 1 : ℝ))) *
            ((thetaNat n - x) + (thetaNat n - (n + 1 : ℝ))) :=
        mul_nonneg hstep hsum
      rw [primeArea_eq_center_add_square, primeArea_eq_center_add_square]
      nlinarith

/-- Positivity on one entire unit interval is equivalent to positivity of its explicit minimum. -/
theorem positive_on_unitInterval_iff (n : ℕ) :
    (∀ x ∈ Icc (n : ℝ) (n + 1 : ℝ), 0 < primeArea n x) ↔
      0 < unitIntervalMinimum n := by
  constructor
  · intro hpos
    unfold unitIntervalMinimum
    by_cases hleft : thetaNat n ≤ (n : ℝ)
    · simp only [hleft, if_true]
      apply hpos n
      constructor
      · exact le_rfl
      · norm_num
    · simp only [hleft, if_false]
      have hleft' : (n : ℝ) < thetaNat n := lt_of_not_ge hleft
      by_cases hright : thetaNat n ≤ (n + 1 : ℝ)
      · simp only [hright, if_true]
        have hcenter : thetaNat n ∈ Icc (n : ℝ) (n + 1 : ℝ) :=
          ⟨hleft'.le, hright⟩
        have h := hpos (thetaNat n) hcenter
        simpa [primeArea_eq_center_add_square] using h
      · simp only [hright, if_false]
        apply hpos (n + 1 : ℝ)
        constructor
        · norm_num
        · exact le_rfl
  · intro hmin x hx
    exact lt_of_lt_of_le hmin (unitIntervalMinimum_le_primeArea n hx)

/-- The exact discrete finite-prime target induced by Johnston's sign criterion. -/
def DiscreteJohnstonCriterion : Prop :=
  ∀ n : ℕ, 2 ≤ n → 0 < unitIntervalMinimum n

/-- The discrete criterion is exactly positivity of every genuine prime-prefix unit parabola. -/
theorem discreteJohnstonCriterion_iff :
    DiscreteJohnstonCriterion ↔
      ∀ n : ℕ, 2 ≤ n →
        ∀ x ∈ Icc (n : ℝ) (n + 1 : ℝ), 0 < primeArea n x := by
  constructor
  · intro hcrit n hn
    exact (positive_on_unitInterval_iff n).2 (hcrit n hn)
  · intro hpos n hn
    exact (positive_on_unitInterval_iff n).1 (hpos n hn)

#print axioms thetaNat_succ
#print axioms primeMoment_succ
#print axioms primeArea_succ
#print axioms primeArea_endpoint_compatible
#print axioms primeArea_eq_center_add_square
#print axioms primeCenter_le_primeArea
#print axioms unitIntervalMinimum_le_primeArea
#print axioms positive_on_unitInterval_iff
#print axioms discreteJohnstonCriterion_iff

end

end Millennium.RH.ChebyshevAreaPrimeFinite