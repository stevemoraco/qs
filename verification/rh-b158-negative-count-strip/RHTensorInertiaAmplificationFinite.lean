import Mathlib

/-!
# RH B158B tensor-inertia amplification finite core

Finite sign combinatorics only.

A single Hermitian positive/negative eigenpair generates `2^m` tensor words at
tensor order `m`; exactly half have negative sign.  This is the finite counting
shadow behind the B158B observation that one resolved BGST indefinite pair can
be amplified internally to exponentially many negative tensor directions.

This file does **not** formalize matrix tensor products, spectral theorems,
contour Hankel matrices, zeta zeros, primes, or RH.
-/

namespace RHTensorInertiaAmplificationFinite

/-- `(positive words, negative words)` obtained by repeatedly tensoring one
positive and one negative sign. -/
def signCounts : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 =>
      let c := signCounts n
      (c.1 + c.2, c.1 + c.2)

/-- At positive tensor order, exactly half of the `2^(n+1)` sign words are
positive and half negative. -/
theorem signCounts_succ (n : ℕ) :
    signCounts (n + 1) = (2 ^ n, 2 ^ n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [signCounts, ih, pow_succ, Nat.mul_two]

/-- Negative sign-word count for the one-positive/one-negative tensor pair. -/
def negativeWords (m : ℕ) : ℕ := (signCounts m).2

/-- Exact exponential negative-count amplification. -/
theorem negativeWords_succ (n : ℕ) :
    negativeWords (n + 1) = 2 ^ n := by
  have h := congrArg Prod.snd (signCounts_succ n)
  simpa [negativeWords] using h

/-- The amplified negative count is nonzero at every positive tensor order. -/
theorem negativeWords_positive (n : ℕ) :
    0 < negativeWords (n + 1) := by
  rw [negativeWords_succ]
  positivity

/-- Positive rescaling preserves the sign of an eigenvalue.  Hence sign-count
tensor amplification is deliberately blind to eigenvalue depth. -/
theorem positive_scaling_preserves_negative_sign
    {c x : ℝ} (hc : 0 < c) :
    c * x < 0 ↔ x < 0 := by
  constructor
  · intro h
    by_contra hx
    have hx0 : 0 ≤ x := le_of_not_gt hx
    have : 0 ≤ c * x := mul_nonneg hc.le hx0
    linarith
  · intro hx
    exact mul_neg_of_pos_of_neg hc hx

/-- The one-positive/one-negative two-direction tensor step always produces one
positive and one negative mixed-sign child. -/
theorem one_pair_tensor_step_signs
    {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    a * a > 0 ∧ b * b > 0 ∧ a * b < 0 ∧ b * a < 0 := by
  constructor
  · exact mul_pos ha ha
  constructor
  · exact mul_pos_of_neg_of_neg hb hb
  constructor
  · exact mul_neg_of_pos_of_neg ha hb
  · exact mul_neg_of_neg_of_pos hb ha

#print axioms signCounts_succ
#print axioms negativeWords_succ
#print axioms negativeWords_positive
#print axioms positive_scaling_preserves_negative_sign
#print axioms one_pair_tensor_step_signs

end RHTensorInertiaAmplificationFinite
