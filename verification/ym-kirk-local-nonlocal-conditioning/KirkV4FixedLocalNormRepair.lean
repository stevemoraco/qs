import Mathlib

namespace Millennium.YangMills

/-- Upper-right coefficient of an iterated two-degree triangular block. -/
def triangularTransfer (a c b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a * triangularTransfer a c b n + b * c ^ n

/-- A self-contained monotonicity lemma for natural powers of nonnegative reals. -/
theorem real_pow_mono_of_nonneg
    (a b : ℝ)
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hb : 0 ≤ b := le_trans ha hab
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg hb n)

/-- Exact closed form for Kirk v4's degree-5 to degree-7 local block. -/
theorem triangularTransfer_five_seven_closed
    (b : ℝ) (n : ℕ) :
    triangularTransfer (1 / 2) (1 / 8) b n =
      (8 * b / 3) * ((1 / 2 : ℝ) ^ n - (1 / 8 : ℝ) ^ n) := by
  induction n with
  | zero => simp [triangularTransfer]
  | succ n ih =>
      simp [triangularTransfer, ih, pow_succ]
      ring

/-- Exact closed form for Kirk v4's degree-6 to degree-8 local block. -/
theorem triangularTransfer_six_eight_closed
    (b : ℝ) (n : ℕ) :
    triangularTransfer (1 / 4) (1 / 16) b n =
      (16 * b / 3) * ((1 / 4 : ℝ) ^ n - (1 / 16 : ℝ) ^ n) := by
  induction n with
  | zero => simp [triangularTransfer]
  | succ n ih =>
      simp [triangularTransfer, ih, pow_succ]
      ring

/-- The degree-5/7 transfer is uniformly bounded by a fixed multiple of the
leading `2⁻ⁿ` diagonal decay. -/
theorem triangularTransfer_five_seven_bound
    (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    triangularTransfer (1 / 2) (1 / 8) b n ≤
      (8 * b / 3) * (1 / 2 : ℝ) ^ n := by
  rw [triangularTransfer_five_seven_closed]
  have hsmall : 0 ≤ (1 / 8 : ℝ) ^ n := by positivity
  have hcoef : 0 ≤ 8 * b / 3 := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hcoef

/-- The degree-6/8 transfer is uniformly bounded by a fixed multiple of the
leading `4⁻ⁿ` diagonal decay. -/
theorem triangularTransfer_six_eight_bound
    (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    triangularTransfer (1 / 4) (1 / 16) b n ≤
      (16 * b / 3) * (1 / 4 : ℝ) ^ n := by
  rw [triangularTransfer_six_eight_closed]
  have hsmall : 0 ≤ (1 / 16 : ℝ) ^ n := by positivity
  have hcoef : 0 ≤ 16 * b / 3 := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hcoef

/-- Complete row envelope for the displayed degree-5/7 block. -/
theorem five_seven_row_envelope
    (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    (1 / 2 : ℝ) ^ n + triangularTransfer (1 / 2) (1 / 8) b n ≤
      (1 + 8 * b / 3) * (1 / 2 : ℝ) ^ n := by
  have h := triangularTransfer_five_seven_bound b hb n
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

/-- Complete row envelope for the displayed degree-6/8 block. -/
theorem six_eight_row_envelope
    (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    (1 / 4 : ℝ) ^ n + triangularTransfer (1 / 4) (1 / 16) b n ≤
      (1 + 16 * b / 3) * (1 / 4 : ℝ) ^ n := by
  have h := triangularTransfer_six_eight_bound b hb n
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n]

/-- The faster degree-6/8 row can also be charged to the common `2⁻ⁿ` local
macrostep decay. -/
theorem six_eight_row_charged_to_half_power
    (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    (1 / 4 : ℝ) ^ n + triangularTransfer (1 / 4) (1 / 16) b n ≤
      (1 + 16 * b / 3) * (1 / 2 : ℝ) ^ n := by
  have hrow := six_eight_row_envelope b hb n
  have hpow : (1 / 4 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    real_pow_mono_of_nonneg (1 / 4) (1 / 2) (by norm_num) (by norm_num) n
  have hcoef : 0 ≤ 1 + 16 * b / 3 := by positivity
  exact le_trans hrow (mul_le_mul_of_nonneg_left hpow hcoef)

/--
A fixed one-step contraction norm has the correct order of quantifiers.  If a
nonnegative scalar envelope contracts by the same `q` at every step, then its
`n`-step value is bounded by `q^n` times the initial value.  No scale-dependent
renorming is introduced after iteration.
-/
theorem fixed_norm_geometric_iteration
    (x : ℕ → ℝ)
    (q : ℝ)
    (hq : 0 ≤ q)
    (hstep : ∀ n, x (n + 1) ≤ q * x n) :
    ∀ n, x n ≤ q ^ n * x 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        x (n + 1) ≤ q * x n := hstep n
        _ ≤ q * (q ^ n * x 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * x 0 := by rw [pow_succ]; ring

#print axioms real_pow_mono_of_nonneg
#print axioms triangularTransfer_five_seven_closed
#print axioms triangularTransfer_six_eight_closed
#print axioms triangularTransfer_five_seven_bound
#print axioms triangularTransfer_six_eight_bound
#print axioms five_seven_row_envelope
#print axioms six_eight_row_envelope
#print axioms six_eight_row_charged_to_half_power
#print axioms fixed_norm_geometric_iteration

end Millennium.YangMills
