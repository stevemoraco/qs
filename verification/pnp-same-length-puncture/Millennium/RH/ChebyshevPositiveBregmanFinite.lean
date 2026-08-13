import Mathlib

/-!
# Finite Bregman spine for the positive Chebyshev-excess criterion

For `F(x) = (max x 0)^2 / 2`, the endpoint subgradient `max b 0`
obeys the exact convex decomposition

  max(b,0) * (b-a) = F(b)-F(a) + D(a,b),

with `D(a,b) >= 0`.

A weighted finite Abel transform then separates endpoint energy, decreasing-weight
energy, drift energy, and Bregman residual. This is finite algebra only: no
primes, Stieltjes integration, infinite series, zeta zeros, or RH are imported.
-/

namespace Millennium.RH.ChebyshevPositiveBregman

open Finset

def positivePart (x : ℝ) : ℝ := max x 0

def positiveEnergy (x : ℝ) : ℝ := positivePart x ^ 2 / 2

def bregmanResidual (a b : ℝ) : ℝ :=
  positivePart b * (b - a) - (positiveEnergy b - positiveEnergy a)

theorem positiveEnergy_nonneg (x : ℝ) : 0 ≤ positiveEnergy x := by
  unfold positiveEnergy
  positivity

theorem bregmanResidual_nonneg (a b : ℝ) :
    0 ≤ bregmanResidual a b := by
  unfold bregmanResidual positiveEnergy positivePart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      nlinarith [sq_nonneg (b - a)]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha' hb
      nlinarith
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right hb']
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      positivity
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      norm_num

theorem bregman_step_identity (a b : ℝ) :
    positivePart b * (b - a) =
      positiveEnergy b - positiveEnergy a + bregmanResidual a b := by
  unfold bregmanResidual
  ring

theorem positiveEnergy_mono {a b : ℝ} (hab : a ≤ b) :
    positiveEnergy a ≤ positiveEnergy b := by
  unfold positiveEnergy positivePart
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    by_cases ha : 0 ≤ a
    · rw [max_eq_left ha]
      have hsum : 0 ≤ a + b := add_nonneg ha hb
      have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
      nlinarith [mul_nonneg hdiff hsum]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [max_eq_right ha']
      positivity
  · have hb' : b ≤ 0 := le_of_not_ge hb
    have ha' : a ≤ 0 := hab.trans hb'
    rw [max_eq_right ha', max_eq_right hb']

theorem driftEnergy_nonneg {pre post : ℝ} (hpre : pre ≤ post) :
    0 ≤ positiveEnergy post - positiveEnergy pre := by
  exact sub_nonneg.mpr (positiveEnergy_mono hpre)

theorem weighted_energy_abel
    (energy weight : ℕ → ℝ) (n : ℕ) :
    (∑ i in range (n + 1),
        weight i * (energy (i + 1) - energy i)) =
      weight n * energy (n + 1) - weight 0 * energy 0 +
        ∑ i in range n,
          (weight i - weight (i + 1)) * energy (i + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      ring

theorem weighted_transition_decomposition
    (post pre weight : ℕ → ℝ) (n : ℕ) :
    (∑ i in range (n + 1),
        weight i *
          (positivePart (post (i + 1)) * (post (i + 1) - pre i))) =
      weight n * positiveEnergy (post (n + 1)) -
          weight 0 * positiveEnergy (post 0) +
        (∑ i in range n,
          (weight i - weight (i + 1)) *
            positiveEnergy (post (i + 1))) +
        (∑ i in range (n + 1),
          weight i * (positiveEnergy (post i) - positiveEnergy (pre i))) +
        (∑ i in range (n + 1),
          weight i * bregmanResidual (pre i) (post (i + 1))) := by
  have hstep : ∀ i : ℕ,
      weight i *
          (positivePart (post (i + 1)) * (post (i + 1) - pre i)) =
        weight i *
            (positiveEnergy (post (i + 1)) - positiveEnergy (post i)) +
          weight i *
            (positiveEnergy (post i) - positiveEnergy (pre i)) +
          weight i * bregmanResidual (pre i) (post (i + 1)) := by
    intro i
    rw [bregman_step_identity]
    ring
  calc
    (∑ i in range (n + 1),
        weight i *
          (positivePart (post (i + 1)) * (post (i + 1) - pre i))) =
        ∑ i in range (n + 1),
          (weight i *
              (positiveEnergy (post (i + 1)) - positiveEnergy (post i)) +
            weight i *
              (positiveEnergy (post i) - positiveEnergy (pre i)) +
            weight i * bregmanResidual (pre i) (post (i + 1))) := by
          apply sum_congr rfl
          intro i hi
          exact hstep i
    _ =
        (∑ i in range (n + 1),
          weight i *
            (positiveEnergy (post (i + 1)) - positiveEnergy (post i))) +
        (∑ i in range (n + 1),
          weight i *
            (positiveEnergy (post i) - positiveEnergy (pre i))) +
        (∑ i in range (n + 1),
          weight i * bregmanResidual (pre i) (post (i + 1))) := by
          simp only [sum_add_distrib]
          ring
    _ =
      weight n * positiveEnergy (post (n + 1)) -
          weight 0 * positiveEnergy (post 0) +
        (∑ i in range n,
          (weight i - weight (i + 1)) *
            positiveEnergy (post (i + 1))) +
        (∑ i in range (n + 1),
          weight i * (positiveEnergy (post i) - positiveEnergy (pre i))) +
        (∑ i in range (n + 1),
          weight i * bregmanResidual (pre i) (post (i + 1))) := by
          rw [weighted_energy_abel]

#print axioms positiveEnergy_nonneg
#print axioms bregmanResidual_nonneg
#print axioms bregman_step_identity
#print axioms positiveEnergy_mono
#print axioms driftEnergy_nonneg
#print axioms weighted_energy_abel
#print axioms weighted_transition_decomposition

end Millennium.RH.ChebyshevPositiveBregman
