import Mathlib

namespace Millennium.YangMills

/--
A fixed-order Faà-di-Bruno envelope for three marked derivative levels.

If one-step derivative constants are bounded by `B >= 1` and the first three
macrostep derivative magnitudes satisfy the standard scalar chain-rule
majorants, then after `n` compositions the order-`m` magnitude is bounded by
`(6 B)^(m n)` for `m = 1,2,3`.

This is deliberately a scalar/envelope theorem. To apply it to a rooted
polymer norm one must separately prove that the normed derivatives satisfy the
three displayed recurrence inequalities without a volume factor or loss of the
support exponent.
-/
theorem macrostep_fixed_order_exponential_envelope
    (B : ℝ) (hB : 1 ≤ B)
    (d1 d2 d3 : ℕ → ℝ)
    (hpos1 : ∀ n, 0 ≤ d1 n)
    (hpos2 : ∀ n, 0 ≤ d2 n)
    (h01 : d1 0 ≤ 1)
    (h02 : d2 0 ≤ 1)
    (h03 : d3 0 ≤ 1)
    (hstep1 : ∀ n, d1 (n + 1) ≤ B * d1 n)
    (hstep2 : ∀ n, d2 (n + 1) ≤ B * d2 n + B * (d1 n) ^ 2)
    (hstep3 : ∀ n,
      d3 (n + 1) ≤
        B * d3 n + 3 * B * d1 n * d2 n + B * (d1 n) ^ 3) :
    ∀ n,
      d1 n ≤ (6 * B) ^ n ∧
      d2 n ≤ (6 * B) ^ (2 * n) ∧
      d3 n ≤ (6 * B) ^ (3 * n) := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hBB : B ≤ B ^ 2 := by
    have haux : 0 ≤ B * (B - 1) := mul_nonneg hB0 (sub_nonneg.mpr hB)
    nlinarith
  have hB2B3 : B ^ 2 ≤ B ^ 3 := by
    calc
      B ^ 2 = B ^ 2 * 1 := by ring
      _ ≤ B ^ 2 * B := mul_le_mul_of_nonneg_left hB (sq_nonneg B)
      _ = B ^ 3 := by ring
  have hcoef1 : B ≤ 6 * B := by nlinarith
  have hcoef2 : 2 * B ≤ (6 * B) ^ 2 := by nlinarith [hBB]
  have hcoef3 : 5 * B ≤ (6 * B) ^ 3 := by nlinarith [hBB, hB2B3]
  intro n
  induction n with
  | zero =>
      constructor
      · simpa using h01
      constructor
      · simpa using h02
      · simpa using h03
  | succ n ih =>
      rcases ih with ⟨ih1, ih2, ih3⟩
      have hp1 : 0 ≤ (6 * B) ^ n := by positivity
      have hp2 : 0 ≤ (6 * B) ^ (2 * n) := by positivity
      have hp3 : 0 ≤ (6 * B) ^ (3 * n) := by positivity
      have hsq : (d1 n) ^ 2 ≤ ((6 * B) ^ n) ^ 2 := by
        have hprod :
            0 ≤ (((6 * B) ^ n) - d1 n) * (((6 * B) ^ n) + d1 n) :=
          mul_nonneg (sub_nonneg.mpr ih1) (add_nonneg hp1 (hpos1 n))
        nlinarith
      have hprod12 :
          d1 n * d2 n ≤ (6 * B) ^ n * (6 * B) ^ (2 * n) :=
        mul_le_mul ih1 ih2 (hpos2 n) hp1
      have hcube : (d1 n) ^ 3 ≤ ((6 * B) ^ n) ^ 3 := by
        calc
          (d1 n) ^ 3 = d1 n * (d1 n) ^ 2 := by ring
          _ ≤ (6 * B) ^ n * (((6 * B) ^ n) ^ 2) :=
            mul_le_mul ih1 hsq (sq_nonneg (d1 n)) hp1
          _ = ((6 * B) ^ n) ^ 3 := by ring
      have hpow_sq : ((6 * B) ^ n) ^ 2 = (6 * B) ^ (2 * n) := by
        rw [pow_two, ← pow_add]
        congr 1
        omega
      have hpow_prod :
          (6 * B) ^ n * (6 * B) ^ (2 * n) = (6 * B) ^ (3 * n) := by
        rw [← pow_add]
        congr 1
        omega
      have hpow_cube : ((6 * B) ^ n) ^ 3 = (6 * B) ^ (3 * n) := by
        calc
          ((6 * B) ^ n) ^ 3 = (6 * B) ^ n * (6 * B) ^ n * (6 * B) ^ n := by ring
          _ = (6 * B) ^ (n + n) * (6 * B) ^ n := by rw [pow_add]
          _ = (6 * B) ^ ((n + n) + n) := by rw [← pow_add]
          _ = (6 * B) ^ (3 * n) := by
            congr 1
            omega
      constructor
      · calc
          d1 (n + 1) ≤ B * d1 n := hstep1 n
          _ ≤ B * (6 * B) ^ n := mul_le_mul_of_nonneg_left ih1 hB0
          _ ≤ (6 * B) * (6 * B) ^ n :=
            mul_le_mul_of_nonneg_right hcoef1 hp1
          _ = (6 * B) ^ (n + 1) := by rw [pow_succ]; ring
      constructor
      · calc
          d2 (n + 1) ≤ B * d2 n + B * (d1 n) ^ 2 := hstep2 n
          _ ≤ B * (6 * B) ^ (2 * n) + B * (((6 * B) ^ n) ^ 2) :=
            add_le_add
              (mul_le_mul_of_nonneg_left ih2 hB0)
              (mul_le_mul_of_nonneg_left hsq hB0)
          _ = 2 * B * (6 * B) ^ (2 * n) := by rw [hpow_sq]; ring
          _ ≤ (6 * B) ^ 2 * (6 * B) ^ (2 * n) :=
            mul_le_mul_of_nonneg_right hcoef2 hp2
          _ = (6 * B) ^ (2 * (n + 1)) := by
            rw [show 2 * (n + 1) = 2 + 2 * n by omega, pow_add]
      · have ht1 : B * d3 n ≤ B * (6 * B) ^ (3 * n) :=
          mul_le_mul_of_nonneg_left ih3 hB0
        have ht2 :
            3 * B * d1 n * d2 n ≤
              3 * B * ((6 * B) ^ n * (6 * B) ^ (2 * n)) := by
          calc
            3 * B * d1 n * d2 n = (3 * B) * (d1 n * d2 n) := by ring
            _ ≤ (3 * B) * ((6 * B) ^ n * (6 * B) ^ (2 * n)) :=
              mul_le_mul_of_nonneg_left hprod12 (by positivity)
            _ = 3 * B * ((6 * B) ^ n * (6 * B) ^ (2 * n)) := by ring
        have ht3 : B * (d1 n) ^ 3 ≤ B * (((6 * B) ^ n) ^ 3) :=
          mul_le_mul_of_nonneg_left hcube hB0
        calc
          d3 (n + 1) ≤
              B * d3 n + 3 * B * d1 n * d2 n + B * (d1 n) ^ 3 := hstep3 n
          _ ≤ B * (6 * B) ^ (3 * n) +
                3 * B * ((6 * B) ^ n * (6 * B) ^ (2 * n)) +
                B * (((6 * B) ^ n) ^ 3) :=
            add_le_add (add_le_add ht1 ht2) ht3
          _ = 5 * B * (6 * B) ^ (3 * n) := by
            rw [hpow_prod, hpow_cube]
            ring
          _ ≤ (6 * B) ^ 3 * (6 * B) ^ (3 * n) :=
            mul_le_mul_of_nonneg_right hcoef3 hp3
          _ = (6 * B) ^ (3 * (n + 1)) := by
            rw [show 3 * (n + 1) = 3 + 3 * n by omega, pow_add]

/--
A dyadic macrostep translation: the fixed-order envelope at `n` dyadic
one-step compositions is a finite power of `L = 2^n` whenever `6 B` itself is
bounded by a dyadic power `2^q`.
-/
theorem macrostep_envelope_is_polynomial_in_dyadic_length
    (B : ℝ) (q m n : ℕ)
    (hB0 : 0 ≤ B)
    (hbase : 6 * B ≤ (2 : ℝ) ^ q) :
    (6 * B) ^ (m * n) ≤ ((2 : ℝ) ^ n) ^ (m * q) := by
  have hpow : (6 * B) ^ (m * n) ≤ ((2 : ℝ) ^ q) ^ (m * n) := by
    exact pow_le_pow_left₀ (by positivity) hbase _
  calc
    (6 * B) ^ (m * n) ≤ ((2 : ℝ) ^ q) ^ (m * n) := hpow
    _ = (2 : ℝ) ^ (q * (m * n)) := by rw [← pow_mul]
    _ = (2 : ℝ) ^ (n * (m * q)) := by
      congr 1
      ring
    _ = ((2 : ℝ) ^ n) ^ (m * q) := by rw [pow_mul]

#print axioms macrostep_fixed_order_exponential_envelope
#print axioms macrostep_envelope_is_polynomial_in_dyadic_length

end Millennium.YangMills
