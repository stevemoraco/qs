import Mathlib

/-!
# PNP two-row Bernoulli parity-hash optimum

This file formalizes finite real and natural-number arithmetic extracted from
an audit of a RepSAT repetition-syndrome tester. It does not formalize
probability spaces, binomial distributions, Chebyshev's inequality, parity
circuits, SAT, NP, hardness magnification, or P versus NP.
-/

namespace MillenniumBraid
namespace B2Round42PNP

/-- Raw miss probability of two independent product Bernoulli parity rows,
written in terms of their biases `a = 1 - 2p₁`, `b = 1 - 2p₂`. -/
noncomputable def rawMiss (a b : ℝ) (w : ℕ) : ℝ :=
  ((1 + a ^ w) * (1 + b ^ w)) / 4

/-- The weight-one and weight-two error constraints alone force the exact
upper bound on the sum of the two row biases. -/
theorem bias_sum_upper_of_weight_one_two
    {a b : ℝ}
    (h₁ : (1 + a) * (1 + b) ≤ (4 : ℝ) / 3)
    (h₂ : (1 + a ^ 2) * (1 + b ^ 2) ≤ (4 : ℝ) / 3) :
    a + b ≤ (Real.sqrt 5 - 1) / 3 := by
  let s : ℝ := a + b
  let t : ℝ := a * b
  change s ≤ (Real.sqrt 5 - 1) / 3
  have hst : s + t ≤ (1 : ℝ) / 3 := by
    dsimp [s, t]
    nlinarith [h₁]
  by_cases hslow : s ≤ -(2 : ℝ) / 3
  · have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  · have hslo : -(2 : ℝ) / 3 < s := lt_of_not_ge hslow
    let u : ℝ := (1 : ℝ) / 3 - s
    have htu : t ≤ u := by
      dsimp [u]
      linarith
    have hu1 : u < 1 := by
      dsimp [u]
      linarith
    have hsum : t + u - 2 < 0 := by
      linarith
    have hfactor : 0 ≤ (t - u) * (t + u - 2) :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr htu) (le_of_lt hsum)
    have hcomp : u ^ 2 - 2 * u ≤ t ^ 2 - 2 * t := by
      nlinarith [hfactor]
    have h₂st : s ^ 2 - 2 * t + t ^ 2 ≤ (1 : ℝ) / 3 := by
      dsimp [s, t]
      nlinarith [h₂]
    have hpoly : 9 * s ^ 2 + 6 * s - 4 ≤ 0 := by
      dsimp [u] at hcomp
      nlinarith [h₂st, hcomp]
    have hsqrt0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
      norm_num
    by_contra hnot
    have hsgt : (Real.sqrt 5 - 1) / 3 < s := lt_of_not_ge hnot
    have hfac1 : 0 < 3 * s + 1 - Real.sqrt 5 := by
      linarith
    have hsqrt2 : 2 ≤ Real.sqrt 5 := by
      nlinarith
    have hfac2 : 0 < 3 * s + 1 + Real.sqrt 5 := by
      nlinarith
    have hpos :
        0 < (3 * s + 1 - Real.sqrt 5) *
          (3 * s + 1 + Real.sqrt 5) :=
      mul_pos hfac1 hfac2
    nlinarith [hpos]

/-- Translating the bias bound back to row densities gives the exact
architecture lower bound `(7 - sqrt 5) / 6`. -/
theorem two_row_density_lower_bound
    {a b : ℝ}
    (h₁ : (1 + a) * (1 + b) ≤ (4 : ℝ) / 3)
    (h₂ : (1 + a ^ 2) * (1 + b ^ 2) ≤ (4 : ℝ) / 3) :
    (7 - Real.sqrt 5) / 6 ≤ (1 - a) / 2 + (1 - b) / 2 := by
  have hs := bias_sum_upper_of_weight_one_two h₁ h₂
  linarith

/-- Exact biases for the near-optimal rational construction. -/
def rationalA : ℝ := (277 : ℝ) / 500

def rationalB : ℝ := -(71 : ℝ) / 500

/-- Exact worst raw miss at syndrome weight one. -/
theorem rational_weight_one :
    rawMiss rationalA rationalB 1 = (333333 : ℝ) / 1000000 := by
  norm_num [rawMiss, rationalA, rationalB]

/-- Weight two is strictly easier for the rational pair. -/
theorem rational_weight_two_lt_weight_one :
    rawMiss rationalA rationalB 2 < (333333 : ℝ) / 1000000 := by
  norm_num [rawMiss, rationalA, rationalB]

/-- The elementary odd-tail envelope lies below the weight-one miss. -/
theorem rational_odd_tail_envelope :
    (1 + ((277 : ℝ) / 500) ^ 3) / 4 <
      (333333 : ℝ) / 1000000 := by
  norm_num

/-- The elementary even-tail envelope is the weight-two value and lies below
weight one. -/
theorem rational_even_tail_envelope :
    ((1 + ((277 : ℝ) / 500) ^ 2) *
        (1 + ((71 : ℝ) / 500) ^ 2)) / 4 <
      (333333 : ℝ) / 1000000 := by
  norm_num

/-- The two raw support densities add to exactly `397/500`. -/
theorem rational_density_identity :
    (223 : ℝ) / 1000 + (571 : ℝ) / 1000 = (397 : ℝ) / 500 := by
  norm_num

/-- Chebyshev with a `708 sqrt(d)` cap gives per-row failure at most this
exact rational number. -/
theorem cap_failure_constant_identity :
    (1 : ℝ) / (4 * 708 ^ 2) = (1 : ℝ) / 2005056 := by
  norm_num

/-- The full separate-conditioning denominator still leaves pointwise error
strictly below one third. -/
theorem rational_conditioned_error_lt_third :
    ((333333 : ℝ) / 1000000) /
        (1 - (1 : ℝ) / 2005056) ^ 2 < (1 : ℝ) / 3 := by
  norm_num

/-- Scaled support-cap addition. The natural `r` is intended to dominate
`sqrt(d)`; that analytic relation is deliberately outside this arithmetic
firewall. -/
theorem scaled_support_cap_add
    {d r t₁ t₂ : ℕ}
    (h₁ : 1000 * t₁ ≤ 223 * d + 708000 * r + 1000)
    (h₂ : 1000 * t₂ ≤ 571 * d + 708000 * r + 1000) :
    1000 * (t₁ + t₂) ≤ 794 * d + 1416000 * r + 2000 := by
  omega

/-- Scaled gate ledger after adding two parity trees, two copies of the `m`
representative budget, and two final gates. -/
theorem scaled_gate_budget
    {d m r s t₁ t₂ : ℕ}
    (h₁ : 1000 * t₁ ≤ 223 * d + 708000 * r + 1000)
    (h₂ : 1000 * t₂ ≤ 571 * d + 708000 * r + 1000) :
    1000 * (s + t₁ + t₂ + 2 * m + 2) ≤
      1000 * s + 794 * d + 1416000 * r + 2000 * m + 4000 := by
  have hsum := scaled_support_cap_add h₁ h₂
  omega

#print axioms bias_sum_upper_of_weight_one_two
#print axioms two_row_density_lower_bound
#print axioms rational_weight_one
#print axioms rational_weight_two_lt_weight_one
#print axioms rational_odd_tail_envelope
#print axioms rational_even_tail_envelope
#print axioms rational_density_identity
#print axioms cap_failure_constant_identity
#print axioms rational_conditioned_error_lt_third
#print axioms scaled_support_cap_add
#print axioms scaled_gate_budget

end B2Round42PNP
end MillenniumBraid
