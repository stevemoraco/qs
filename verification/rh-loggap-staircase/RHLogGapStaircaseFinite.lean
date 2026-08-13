import Mathlib

/-!
# Finite cores for the RH logarithmic-gap staircase firewall

This file formalizes only finite real-algebraic consequences of the defect
recurrence and Johnston-margin bookkeeping. It does not formalize the implicit
real event sequence, asymptotic integral comparisons, Beurling generalized
primes, Johnston's analytic theorem, the zeta function, or RH.
-/

open scoped BigOperators

namespace Millennium
namespace RHLogGapStaircase

/-- The accumulated logarithmic event weight through index `n`. -/
def prefixMass (weight : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k in Finset.range (n + 1), weight k

/-- Event location minus accumulated logarithmic weight. -/
def prefixDefect (location weight : ℕ → ℝ) (n : ℕ) : ℝ :=
  location n - prefixMass weight n

/-- If the next gap is the next logarithmic weight minus `delta`, then the
prefix defect drops by exactly `delta`. -/
theorem prefixDefect_step
    (location weight delta : ℕ → ℝ) (n : ℕ)
    (hgap : location (n + 1) - location n =
      weight (n + 1) - delta n) :
    prefixDefect location weight (n + 1) =
      prefixDefect location weight n - delta n := by
  simp only [prefixDefect, prefixMass, Finset.sum_range_succ]
  linarith

/-- Abstract scalar form of the same one-step defect identity. -/
theorem defect_step
    (current next gap nextWeight delta : ℝ)
    (hnext : next = current + gap - nextWeight)
    (hgap : gap = nextWeight - delta) :
    next = current - delta := by
  linarith

/-- Iterating the exact defect recurrence produces the finite telescope. -/
theorem defect_telescope
    (defect delta : ℕ → ℝ)
    (hrec : ∀ n, defect (n + 1) = defect n - delta n)
    (n : ℕ) :
    defect n = defect 0 - ∑ k in Finset.range n, delta k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hrec n, ih, Finset.sum_range_succ]
      ring

/-- Once the cumulative positive drift exceeds the initial reserve plus `B`,
the defect is strictly below `-B`. -/
theorem cumulative_bias_forces_negative
    (defect delta : ℕ → ℝ)
    (hrec : ∀ n, defect (n + 1) = defect n - delta n)
    (n : ℕ) (B : ℝ)
    (hlarge : defect 0 + B < ∑ k in Finset.range n, delta k) :
    defect n < -B := by
  rw [defect_telescope defect delta hrec n]
  linarith

/-- A nonnegative endpoint tax places the prefix floor below the continuous
margin. -/
theorem nonnegative_tax_forces_prefix_below_margin
    (margin prefix tax : ℝ)
    (hdecomp : margin - prefix = tax)
    (htax : 0 ≤ tax) :
    prefix ≤ margin := by
  linarith

/-- The identity `I = -2M` converts a positive critical integral into a
strictly negative margin. -/
theorem positive_integral_forces_negative_margin
    (integral margin : ℝ)
    (hidentity : integral = -2 * margin)
    (hintegral : 0 < integral) :
    margin < 0 := by
  linarith

/-- Combining positive critical integral with a nonnegative endpoint tax makes
the prefix floor strictly negative. -/
theorem positive_integral_and_tax_force_negative_prefix
    (integral margin prefix tax : ℝ)
    (hidentity : integral = -2 * margin)
    (hdecomp : margin - prefix = tax)
    (hintegral : 0 < integral)
    (htax : 0 ≤ tax) :
    prefix < 0 := by
  have hmargin : margin < 0 :=
    positive_integral_forces_negative_margin integral margin hidentity hintegral
  have hprefix : prefix ≤ margin :=
    nonnegative_tax_forces_prefix_below_margin margin prefix tax hdecomp htax
  exact hprefix.trans_lt hmargin

/-- The square-root endpoint tax is algebraically nonnegative once represented
as a square divided by a positive denominator. -/
theorem square_tax_nonnegative
    (a b denominator : ℝ)
    (hdenominator : 0 < denominator) :
    0 ≤ (a - b) ^ 2 / denominator := by
  positivity

#print axioms prefixDefect_step
#print axioms defect_step
#print axioms defect_telescope
#print axioms cumulative_bias_forces_negative
#print axioms nonnegative_tax_forces_prefix_below_margin
#print axioms positive_integral_forces_negative_margin
#print axioms positive_integral_and_tax_force_negative_prefix
#print axioms square_tax_nonnegative

end RHLogGapStaircase
end Millennium
