import Mathlib

/-!
# Finite square-root queue checkpoint core

This file formalizes only the finite scalar identities used by RH C532.
For `x_+ = max x 0`, a unit-speed downward drift of length `d >= 0`
removes exactly `min d x_+` positive-part workload.  The same identity,
read backwards across a positive jump, gives the exact clipped prime-arrival
formula.  A one-jump/two-drift queue cell then telescopes exactly.

This file does not formalize primes, Chebyshev functions, the change of
variables `s = 2 sqrt x`, measure/integration, C529B/C530/C531, Suzuki/Landau,
BGST, zeta zeros, or RH.
-/

namespace Millennium.RH.SqrtQueueCheckpoint

/-- Positive part on the reals. -/
def positivePart (x : ℝ) : ℝ := max x 0

/--
Exact clipped loss under a downward drift of length `d >= 0`:

`y_+ - (y-d)_+ = min d y_+`.
-/
theorem clipped_drop (y d : ℝ) (hd : 0 ≤ d) :
    positivePart y - positivePart (y - d) = min d (positivePart y) := by
  unfold positivePart
  by_cases hy : 0 ≤ y
  · rw [max_eq_left hy]
    by_cases hdy : d ≤ y
    · have hyd : 0 ≤ y - d := sub_nonneg.mpr hdy
      rw [max_eq_left hyd, min_eq_left hdy]
      ring
    · have hyd : y ≤ d := le_of_not_ge hdy
      have hyd0 : y - d ≤ 0 := sub_nonpos.mpr hyd
      rw [max_eq_right hyd0, min_eq_right hyd]
      ring
  · have hy0 : y ≤ 0 := le_of_not_ge hy
    have hyd0 : y - d ≤ 0 := by linarith
    rw [max_eq_right hy0, max_eq_right hyd0]
    simp [hd]

/--
Exact clipped positive arrival across an upward jump `jump >= 0`.
Only the part of the jump landing above the threshold is charged.
-/
theorem clipped_jump
    (pre jump threshold : ℝ) (hjump : 0 ≤ jump) :
    positivePart (pre + jump - threshold) - positivePart (pre - threshold) =
      min jump (positivePart (pre + jump - threshold)) := by
  have h := clipped_drop (pre + jump - threshold) jump hjump
  have heq : pre + jump - threshold - jump = pre - threshold := by ring
  rw [heq] at h
  exact h

/-- Exact superlevel length of one unit-speed downward drift segment. -/
theorem drift_superlevel_length
    (w ell threshold : ℝ) (hell : 0 ≤ ell) :
    min ell (positivePart (w - threshold)) =
      positivePart (w - threshold) - positivePart (w - ell - threshold) := by
  have h := clipped_drop (w - threshold) ell hell
  have heq : w - threshold - ell = w - ell - threshold := by ring
  rw [heq] at h
  exact h.symm

/--
One-jump queue balance: the total superlevel length of two unit-speed drift
segments equals endpoint positive-part loss plus the clipped jump arrival.
This is the finite telescoping cell behind the full C532 checkpoint sum.
-/
theorem one_jump_queue_balance
    (w ell₁ jump ell₂ threshold : ℝ)
    (hell₁ : 0 ≤ ell₁) (hell₂ : 0 ≤ ell₂) :
    min ell₁ (positivePart (w - threshold)) +
        min ell₂ (positivePart (w - ell₁ + jump - threshold)) =
      positivePart (w - threshold) -
          positivePart (w - ell₁ + jump - ell₂ - threshold) +
        (positivePart (w - ell₁ + jump - threshold) -
          positivePart (w - ell₁ - threshold)) := by
  have h₁ := drift_superlevel_length w ell₁ threshold hell₁
  have h₂ := drift_superlevel_length (w - ell₁ + jump) ell₂ threshold hell₂
  linarith

/--
The one-jump balance with the jump term rewritten in consumer-minimal clipped
form.  The nonnegativity of the jump is the only extra hypothesis.
-/
theorem one_jump_queue_balance_clipped
    (w ell₁ jump ell₂ threshold : ℝ)
    (hell₁ : 0 ≤ ell₁) (hjump : 0 ≤ jump) (hell₂ : 0 ≤ ell₂) :
    min ell₁ (positivePart (w - threshold)) +
        min ell₂ (positivePart (w - ell₁ + jump - threshold)) =
      positivePart (w - threshold) -
          positivePart (w - ell₁ + jump - ell₂ - threshold) +
        min jump (positivePart (w - ell₁ + jump - threshold)) := by
  rw [one_jump_queue_balance w ell₁ jump ell₂ threshold hell₁ hell₂]
  rw [clipped_jump (w - ell₁) jump threshold hjump]

#print axioms clipped_drop
#print axioms clipped_jump
#print axioms drift_superlevel_length
#print axioms one_jump_queue_balance
#print axioms one_jump_queue_balance_clipped

end Millennium.RH.SqrtQueueCheckpoint
