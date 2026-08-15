import Mathlib

/-!
# RH B134 positive prime-work finite core

Finite real algebra only.

The human B134 argument observes that the ordinary-prime Mertens remainder has
unit negative drift between prime events and only positive jumps at prime events.
For the convex energy `Phi_+(x)=1/2 [x]_+^2`, this turns one-sided area into a
boundary energy plus nonnegative jump work.

This file formalizes only the load-bearing finite algebra: monotonicity of the
positive-square energy, the exact one-step energy ledger, finite telescoping,
and the sharp jump-work sandwich. It contains no primes, integration, Mellin
analysis, zeta, B46, or RH.
-/

open Finset
open scoped BigOperators

namespace RHB134PositivePrimeWorkFinite

/-- Convex positive energy `1/2 [x]_+^2`. -/
def posSq (x : ℝ) : ℝ := (max x 0) ^ 2 / 2

/-- Energy injected by an upward jump of size `a`. -/
def jumpWork (x a : ℝ) : ℝ := posSq (x + a) - posSq x

/-- Energy consumed by unit negative drift over a segment of length `ell`. -/
def segmentMass (x ell : ℝ) : ℝ := posSq x - posSq (x - ell)

@[simp] theorem posSq_nonneg (x : ℝ) : 0 ≤ posSq x := by
  unfold posSq
  positivity

/-- `posSq` is monotone. -/
theorem posSq_mono {x y : ℝ} (hxy : x ≤ y) : posSq x ≤ posSq y := by
  have hm : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
  have hx0 : 0 ≤ max x 0 := le_max_right _ _
  have hy0 : 0 ≤ max y 0 := le_max_right _ _
  have hprod :
      0 ≤ (max y 0 - max x 0) * (max y 0 + max x 0) :=
    mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hy0 hx0)
  unfold posSq
  nlinarith

/-- Upward jumps have nonnegative positive-energy work. -/
theorem jumpWork_nonneg (x a : ℝ) (ha : 0 ≤ a) :
    0 ≤ jumpWork x a := by
  unfold jumpWork
  exact sub_nonneg.mpr (posSq_mono (by linarith))

/-- The exact lower linearization of positive jump work. -/
theorem jumpWork_lower (x a : ℝ) (ha : 0 ≤ a) :
    a * max x 0 ≤ jumpWork x a := by
  by_cases hx : 0 ≤ x
  · have hxa : 0 ≤ x + a := add_nonneg hx ha
    simp [jumpWork, posSq, max_eq_left hx, max_eq_left hxa]
    nlinarith
  · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hj := jumpWork_nonneg x a ha
    simpa [max_eq_right hxle] using hj

/-- The exact upper linearization: the nonlinear correction costs at most
`a^2/2`. -/
theorem jumpWork_upper (x a : ℝ) (ha : 0 ≤ a) :
    jumpWork x a ≤ a * max x 0 + a ^ 2 / 2 := by
  by_cases hx : 0 ≤ x
  · have hxa : 0 ≤ x + a := add_nonneg hx ha
    simp [jumpWork, posSq, max_eq_left hx, max_eq_left hxa]
    nlinarith
  · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    have hxa_le : x + a ≤ a := by linarith
    have hm : max (x + a) 0 ≤ a := max_le hxa_le ha
    have hm0 : 0 ≤ max (x + a) 0 := le_max_right _ _
    have hprod :
        0 ≤ (a - max (x + a) 0) * (a + max (x + a) 0) :=
      mul_nonneg (sub_nonneg.mpr hm) (add_nonneg ha hm0)
    unfold jumpWork posSq
    rw [max_eq_right hxle]
    nlinarith

/-- Negative drift consumes nonnegative positive energy. -/
theorem segmentMass_nonneg (x ell : ℝ) (hell : 0 ≤ ell) :
    0 ≤ segmentMass x ell := by
  unfold segmentMass
  exact sub_nonneg.mpr (posSq_mono (by linarith))

/-- One exact drift+jump step: consumed segment mass equals boundary-energy loss
plus the jump work restoring the next state. -/
theorem one_step_energy_balance
    (x ell a y : ℝ) (hy : y = x - ell + a) :
    segmentMass x ell =
      posSq x - posSq y + jumpWork (x - ell) a := by
  rw [hy]
  unfold segmentMass jumpWork
  ring

/-- Exact finite telescoping energy identity for any drift+jump chain. -/
theorem finite_energy_balance
    (x ell a : ℕ → ℝ)
    (hstep : ∀ i : ℕ, x (i + 1) = x i - ell i + a i)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, segmentMass (x i) (ell i)) =
      posSq (x 0) - posSq (x N) +
        ∑ i ∈ Finset.range N, jumpWork (x i - ell i) (a i) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [one_step_energy_balance (x N) (ell N) (a N) (x (N + 1))
        (hstep N)]
      ring

/-- Summed jump work differs from the linear positive-state work by at most the
sum of the square-jump diagonal costs. -/
theorem finite_jump_work_sandwich
    {ι : Type*} (s : Finset ι) (x a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * max (x i) 0) ≤
      (∑ i ∈ s, jumpWork (x i) (a i)) ∧
    (∑ i ∈ s, jumpWork (x i) (a i)) ≤
      (∑ i ∈ s, a i * max (x i) 0) +
      (∑ i ∈ s, (a i) ^ 2 / 2) := by
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact jumpWork_lower (x i) (a i) (ha i hi)
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact jumpWork_upper (x i) (a i) (ha i hi)

#print axioms posSq_nonneg
#print axioms posSq_mono
#print axioms jumpWork_nonneg
#print axioms jumpWork_lower
#print axioms jumpWork_upper
#print axioms segmentMass_nonneg
#print axioms one_step_energy_balance
#print axioms finite_energy_balance
#print axioms finite_jump_work_sandwich

end RHB134PositivePrimeWorkFinite
