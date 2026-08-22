import Mathlib

/-!
# Finite Bregman spine for the positive Chebyshev-excess criterion

For `F(x) = (max x 0)^2 / 2`, the endpoint subgradient `max b 0`
obeys the exact convex decomposition

  max(b,0) * (b-a) = F(b)-F(a) + D(a,b),

with `D(a,b) >= 0`.

A weighted finite Abel transform then separates endpoint energy, decreasing-weight
energy, drift energy, and Bregman residual.  This is the finite algebra behind an
independent Stieltjes proof of the positive Chebyshev-excess RH equivalent.

This file does not formalize primes, Chebyshev functions, Stieltjes integration,
infinite series, zeta zeros, or RH.
-/

namespace Millennium.RH.ChebyshevPositiveBregman

open Finset

/-- Positive part on the reals. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Convex positive-square energy `F(x) = (x_+)^2 / 2`. -/
def positiveEnergy (x : ℝ) : ℝ := positivePart x ^ 2 / 2

/-- Endpoint Bregman residual for the positive-square energy. -/
def bregmanResidual (a b : ℝ) : ℝ :=
  positivePart b * (b - a) - (positiveEnergy b - positiveEnergy a)

/-- The positive-square energy is nonnegative. -/
theorem positiveEnergy_nonneg (x : ℝ) : 0 ≤ positiveEnergy x := by
  unfold positiveEnergy
  positivity

/-- The endpoint Bregman residual is always nonnegative. -/
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

/-- Exact one-step convex decomposition. -/
theorem bregman_step_identity (a b : ℝ) :
    positivePart b * (b - a) =
      positiveEnergy b - positiveEnergy a + bregmanResidual a b := by
  unfold bregmanResidual
  ring

/-- Positive-square energy is monotone. -/
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

/-- Energy lost during a downward drift is nonnegative. -/
theorem driftEnergy_nonneg {pre post : ℝ} (hpre : pre ≤ post) :
    0 ≤ positiveEnergy post - positiveEnergy pre := by
  exact sub_nonneg.mpr (positiveEnergy_mono hpre)

/-- Finite weighted summation by parts for consecutive energy increments. -/
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

/--
Exact finite transition decomposition.

`post i` is the state after event `i`; `pre i` is the state reached from
`post i` by the intervening downward drift; the next positive jump lands at
`post (i+1)`.  The weighted jump work splits into:

* terminal minus initial energy;
* decreasing-weight energy;
* drift energy;
* nonnegative Bregman residual.
-/
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
