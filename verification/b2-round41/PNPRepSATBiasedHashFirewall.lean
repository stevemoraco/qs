import Mathlib

/-!
# PNP RepSAT biased dual-hash arithmetic firewall

This file formalizes exact rational error margins, the conditioning budget, and
scaled natural-number gate arithmetic from the biased dual-hash construction.
It does not formalize probability spaces, binomial distributions, parity
formulas, Boolean circuits, SAT, NP, or P versus NP.
-/

namespace MillenniumBraid
namespace B2Round41PNPRepSATBiased

/-- Weight-one syndrome miss probability before support conditioning. -/
theorem weight_one_raw_miss :
    ((3 : ℝ) / 4) * ((2 : ℝ) / 5) = (3 : ℝ) / 10 := by
  norm_num

/-- Weight-two syndrome is the worst displayed raw case. -/
theorem weight_two_raw_miss :
    ((5 : ℝ) / 8) * ((13 : ℝ) / 25) = (13 : ℝ) / 40 := by
  norm_num

/-- Uniform bound used for every odd syndrome weight at least three. -/
theorem odd_weight_tail_margin :
    ((9 : ℝ) / 16) * ((1 : ℝ) / 2) < (13 : ℝ) / 40 := by
  norm_num

/-- Uniform bound used for every even syndrome weight at least four. -/
theorem even_weight_tail_margin :
    ((17 : ℝ) / 32) * ((13 : ℝ) / 25) < (13 : ℝ) / 40 := by
  norm_num

/-- Conditioning two independent rows on events of probability at least
`99/100` preserves a strict one-third miss bound when the unconditioned joint
miss is at most `13/40`.  The hypothesis `(p₁*p₂)*q ≤ 13/40` is the
cross-multiplied conditional-probability inequality. -/
theorem conditioned_biased_rows_below_third
    {p₁ p₂ q : ℝ}
    (hp₁ : (99 : ℝ) / 100 ≤ p₁)
    (hp₂ : (99 : ℝ) / 100 ≤ p₂)
    (hq : 0 ≤ q)
    (hjoint : (p₁ * p₂) * q ≤ (13 : ℝ) / 40) :
    q < (1 : ℝ) / 3 := by
  have hp₂0 : 0 ≤ p₂ := by
    linarith
  have hconst : 0 ≤ (99 : ℝ) / 100 := by
    norm_num
  have hprod : (9801 : ℝ) / 10000 ≤ p₁ * p₂ := by
    calc
      (9801 : ℝ) / 10000 =
          ((99 : ℝ) / 100) * ((99 : ℝ) / 100) := by norm_num
      _ ≤ ((99 : ℝ) / 100) * p₂ :=
        mul_le_mul_of_nonneg_left hp₂ hconst
      _ ≤ p₁ * p₂ :=
        mul_le_mul_of_nonneg_right hp₁ hp₂0
  have hscaled : ((9801 : ℝ) / 10000) * q ≤ (p₁ * p₂) * q :=
    mul_le_mul_of_nonneg_right hprod hq
  have hfinal : ((9801 : ℝ) / 10000) * q ≤ (13 : ℝ) / 40 :=
    hscaled.trans hjoint
  nlinarith

/-- The explicit rational conditioning ceiling is strictly below one third. -/
theorem explicit_conditioned_fraction_below_third :
    (130000 : ℝ) / 392040 < (1 : ℝ) / 3 := by
  norm_num

/-- Scaled gate budget.  `r` is an integer upper proxy for `sqrt d`; the two
support-cap hypotheses are the denominator-cleared forms of
`t₁ ≤ d/4 + 5r + 1` and `t₂ ≤ 3d/5 + 5r + 1`. -/
theorem biased_hash_scaled_gate_budget
    {d m t₁ t₂ r s : ℕ}
    (h₁ : 20 * t₁ ≤ 5 * d + 100 * r + 20)
    (h₂ : 5 * t₂ ≤ 3 * d + 25 * r + 5) :
    20 * (s + t₁ + t₂ + 2 * m + 2) ≤
      20 * s + 17 * d + 40 * m + 200 * r + 80 := by
  omega

/-- The leading support coefficient is exactly `17/20`. -/
theorem leading_coefficient_identity :
    (1 : ℝ) / 4 + (3 : ℝ) / 5 = (17 : ℝ) / 20 := by
  norm_num

#print axioms weight_one_raw_miss
#print axioms weight_two_raw_miss
#print axioms odd_weight_tail_margin
#print axioms even_weight_tail_margin
#print axioms conditioned_biased_rows_below_third
#print axioms explicit_conditioned_fraction_below_third
#print axioms biased_hash_scaled_gate_budget
#print axioms leading_coefficient_identity

end B2Round41PNPRepSATBiased
end MillenniumBraid
