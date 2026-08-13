import Mathlib

/-!
# Summable relative-defect product firewall

This file formalizes finite multiplicative estimates used in the cross-problem
research bank.

It proves:

* for `0 ≤ ε ≤ 1/2`, `exp (-2 ε) ≤ 1 - ε`;
* nonnegative relative defects with total finite budget only change an ideal
  multiplicative growth law by a fixed prefactor;
* the contraction-side dual, with the necessary nonnegativity assumption on
  the actual factors;
* a two-factor counterexample showing that the contraction statement is false
  if actual-factor nonnegativity is omitted;
* the exact Navier--Stokes ideal reserve `4 - 2√2 > 1`.

It does **not** formalize Navier--Stokes, Yang--Mills, any cascade construction,
any continuum limit, or any Millennium theorem.
-/

open scoped BigOperators

namespace SummableRelativeDefect

/-- Pointwise logarithmic firewall behind the growth estimate.

The constant `2` is valid on the full interval `0 ≤ x ≤ 1/2`:
`exp (-2x) ≤ 1-x`.
-/
theorem exp_neg_two_mul_le_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by
    linarith
  have hshape : 0 ≤ x * (1 - 2 * x) := by
    exact mul_nonneg hx0 (by linarith)
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    have hdiv : 1 / (1 - x) ≤ 1 + 2 * x := by
      apply (div_le_iff₀ hpos).2
      nlinarith
    simpa [one_div] using hdiv
  have hlinear : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    linarith
  have hlog : -2 * x ≤ Real.log (1 - x) :=
    hlinear.trans (Real.one_sub_inv_le_log_of_pos hpos)
  have hexp := Real.exp_le_exp_of_le hlog
  rw [Real.exp_log hpos] at hexp
  exact hexp

/-- A finite family of defects in `[0,1/2]` has a product bounded below by the
exponential of minus twice its total defect. -/
theorem product_one_sub_lower_exp
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ε : ι → ℝ)
    (hε0 : ∀ i ∈ s, 0 ≤ ε i)
    (hεhalf : ∀ i ∈ s, ε i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i in s, ε i) ≤ ∏ i in s, (1 - ε i) := by
  calc
    Real.exp (-2 * ∑ i in s, ε i) =
        Real.exp (∑ i in s, (-2 * ε i)) := by
          congr 1
          rw [Finset.mul_sum]
    _ = ∏ i in s, Real.exp (-2 * ε i) :=
      Real.exp_sum s (fun i => -2 * ε i)
    _ ≤ ∏ i in s, (1 - ε i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Real.exp_nonneg _
      · intro i hi
        exact exp_neg_two_mul_le_one_sub (hε0 i hi) (hεhalf i hi)

/-- The contraction-side pointwise estimate aggregated over a finite family. -/
theorem product_one_add_upper_exp
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ε : ι → ℝ)
    (hε0 : ∀ i ∈ s, 0 ≤ ε i) :
    (∏ i in s, (1 + ε i)) ≤ Real.exp (∑ i in s, ε i) := by
  calc
    (∏ i in s, (1 + ε i)) ≤ ∏ i in s, Real.exp (ε i) := by
      apply Finset.prod_le_prod
      · intro i hi
        linarith [hε0 i hi]
      · intro i hi
        simpa [add_comm] using Real.add_one_le_exp (ε i)
    _ = Real.exp (∑ i in s, ε i) := (Real.exp_sum s ε).symm

/-- Finite growth product with a total relative-defect budget.

Only nonnegativity of `g` is algebraically needed; `1 < g` is retained because
that is the supercritical regime in which the theorem is used.
-/
theorem growth_product_lower
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (G ε : ι → ℝ) (g E : ℝ)
    (hg : 1 < g)
    (hε0 : ∀ i ∈ s, 0 ≤ ε i)
    (hεhalf : ∀ i ∈ s, ε i ≤ 1 / 2)
    (hbudget : (∑ i in s, ε i) ≤ E)
    (hG : ∀ i ∈ s, g * (1 - ε i) ≤ G i) :
    Real.exp (-2 * E) * g ^ s.card ≤ ∏ i in s, G i := by
  have hg0 : 0 ≤ g := by
    linarith
  have hpow0 : 0 ≤ g ^ s.card := pow_nonneg hg0 _
  have hexpBudget :
      Real.exp (-2 * E) ≤ Real.exp (-2 * ∑ i in s, ε i) := by
    apply Real.exp_le_exp_of_le
    linarith
  have hdefect := product_one_sub_lower_exp s ε hε0 hεhalf
  have hfactor :
      (∏ i in s, (g * (1 - ε i))) ≤ ∏ i in s, G i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact mul_nonneg hg0 (by linarith [hεhalf i hi])
    · intro i hi
      exact hG i hi
  calc
    Real.exp (-2 * E) * g ^ s.card ≤
        Real.exp (-2 * ∑ i in s, ε i) * g ^ s.card :=
      mul_le_mul_of_nonneg_right hexpBudget hpow0
    _ ≤ (∏ i in s, (1 - ε i)) * g ^ s.card :=
      mul_le_mul_of_nonneg_right hdefect hpow0
    _ = ∏ i in s, (g * (1 - ε i)) := by
      rw [Finset.prod_mul_distrib]
      simp [mul_comm]
    _ ≤ ∏ i in s, G i := hfactor

/-- Finite contraction product with a total relative-defect budget.

The hypotheses `0 ≤ Q i` are essential. Without them, pointwise upper bounds
cannot in general be multiplied in an ordered field.
-/
theorem contraction_product_upper
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (Q ε : ι → ℝ) (q E : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hQ0 : ∀ i ∈ s, 0 ≤ Q i)
    (hε0 : ∀ i ∈ s, 0 ≤ ε i)
    (hbudget : (∑ i in s, ε i) ≤ E)
    (hQ : ∀ i ∈ s, Q i ≤ q * (1 + ε i)) :
    (∏ i in s, Q i) ≤ Real.exp E * q ^ s.card := by
  have hqnonneg : 0 ≤ q := le_of_lt hq0
  have hqpow : 0 ≤ q ^ s.card := pow_nonneg hqnonneg _
  have hcompare :
      (∏ i in s, Q i) ≤ ∏ i in s, (q * (1 + ε i)) := by
    apply Finset.prod_le_prod hQ0
    intro i hi
    exact hQ i hi
  have hdefect := product_one_add_upper_exp s ε hε0
  have hexpBudget :
      Real.exp (∑ i in s, ε i) ≤ Real.exp E :=
    Real.exp_le_exp_of_le hbudget
  calc
    (∏ i in s, Q i) ≤ ∏ i in s, (q * (1 + ε i)) := hcompare
    _ = q ^ s.card * ∏ i in s, (1 + ε i) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ q ^ s.card * Real.exp (∑ i in s, ε i) :=
      mul_le_mul_of_nonneg_left hdefect hqpow
    _ ≤ q ^ s.card * Real.exp E :=
      mul_le_mul_of_nonneg_left hexpBudget hqpow
    _ = Real.exp E * q ^ s.card := by ring

/-- Prefix form of the growth theorem for sequences. -/
theorem growth_prefix_lower
    (G ε : ℕ → ℝ) (g E : ℝ)
    (hg : 1 < g)
    (hε0 : ∀ j, 0 ≤ ε j)
    (hεhalf : ∀ j, ε j ≤ 1 / 2)
    (hbudget : ∀ n, (∑ j in Finset.range n, ε j) ≤ E)
    (hG : ∀ j, g * (1 - ε j) ≤ G j)
    (n : ℕ) :
    Real.exp (-2 * E) * g ^ n ≤ ∏ j in Finset.range n, G j := by
  simpa using growth_product_lower (Finset.range n) G ε g E hg
    (fun i _hi => hε0 i) (fun i _hi => hεhalf i) (hbudget n)
    (fun i _hi => hG i)

/-- Prefix form of the contraction theorem for nonnegative sequences. -/
theorem contraction_prefix_upper
    (Q ε : ℕ → ℝ) (q E : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hQ0 : ∀ j, 0 ≤ Q j)
    (hε0 : ∀ j, 0 ≤ ε j)
    (hbudget : ∀ n, (∑ j in Finset.range n, ε j) ≤ E)
    (hQ : ∀ j, Q j ≤ q * (1 + ε j))
    (n : ℕ) :
    (∏ j in Finset.range n, Q j) ≤ Real.exp E * q ^ n := by
  simpa using contraction_product_upper (Finset.range n) Q ε q E hq0 hq1
    (fun i _hi => hQ0 i) (fun i _hi => hε0 i) (hbudget n)
    (fun i _hi => hQ i)

/-- The informal contraction dual is false without nonnegativity of the actual
factors: two negative factors reverse the intended product control. -/
theorem contraction_without_nonnegativity_counterexample :
    let q : ℝ := 1 / 2
    let Q₀ : ℝ := -1
    let Q₁ : ℝ := -1
    Q₀ ≤ q * (1 + 0) ∧
      Q₁ ≤ q * (1 + 0) ∧
      ¬ (Q₀ * Q₁ ≤ Real.exp 0 * q ^ 2) := by
  norm_num

/-- Exact identity for the ideal Navier--Stokes surrogate gain. -/
theorem ns_ideal_gain_identity :
    (2 / (1 + Real.sqrt 2)) * Real.sqrt 2 =
      4 - 2 * Real.sqrt 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hden : 1 + Real.sqrt 2 ≠ 0 := by
    positivity
  field_simp [hden]
  nlinarith

/-- The ideal Navier--Stokes surrogate gain has a strict reserve above one. -/
theorem ns_ideal_gain_gt_one :
    (1 : ℝ) < 4 - 2 * Real.sqrt 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

#print axioms exp_neg_two_mul_le_one_sub
#print axioms product_one_sub_lower_exp
#print axioms product_one_add_upper_exp
#print axioms growth_product_lower
#print axioms contraction_product_upper
#print axioms growth_prefix_lower
#print axioms contraction_prefix_upper
#print axioms contraction_without_nonnegativity_counterexample
#print axioms ns_ideal_gain_identity
#print axioms ns_ideal_gain_gt_one

end SummableRelativeDefect
