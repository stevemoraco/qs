import Mathlib

/-!
# RH B53G: height-one factorial terminal gap

This file formalizes the finite terminal algebra used after applying Jonathan
Bober's classification of primitive integral factorial ratios of height one.

Human/source boundary (not formalized here): after cancelling common factors,
normalizing the common gcd, and applying Landau's criterion, Bober's Theorem 1.2
places every primitive height-one datum in one of three infinite families or in
one of 52 sporadic cases.  The family entropy estimates and the audit that every
coefficient in Bober's sporadic table is at most `30` are also external inputs.

Kernel-checked here:

* the exact universal gap `1 / 992` contributed by a sporadic period at most 30;
* rigorous numerical comparison of that gap with `log 2` and `(log 3) / 2`;
* the terminal case split combining the three infinite-family bounds and the
  sporadic bound;
* the consequence that an asymptotically sharp family cannot remain at height
  one;
* two elementary geometric inequalities used in the second infinite family.

This is not a formalization of Bober's classification, the entropy integral,
factorial integrality, the zeta function, or RH.
-/

namespace RHB53

/-- Uniform additive entropy gap obtained from the largest sporadic coefficient
`30`: `1 / ((30 + 1) * (30 + 2)) = 1 / 992`. -/
def heightOneGap : ℝ := 1 / 992

/-- The forbidden height-one near-extremal threshold. -/
def heightOneThreshold : ℝ := 1 / 2 + heightOneGap

/-- Mathlib's certified lower bound for `log 2` is well above the uniform
height-one threshold. -/
theorem heightOneThreshold_lt_log_two :
    heightOneThreshold < Real.log 2 := by
  calc
    heightOneThreshold = (497 : ℝ) / 992 := by
      norm_num [heightOneThreshold, heightOneGap]
    _ < (0.6931471803 : ℝ) := by norm_num
    _ < Real.log 2 := Real.log_two_gt_d9

/-- Mathlib's certified lower bound for `log 3` is also strong enough after
halving. -/
theorem heightOneThreshold_lt_half_log_three :
    heightOneThreshold < Real.log 3 / 2 := by
  have hthree : (0.54930614425 : ℝ) < Real.log 3 / 2 := by
    have h := Real.log_three_gt_d9
    norm_num at h ⊢
    linarith
  calc
    heightOneThreshold = (497 : ℝ) / 992 := by
      norm_num [heightOneThreshold, heightOneGap]
    _ < (0.54930614425 : ℝ) := by norm_num
    _ < Real.log 3 / 2 := hthree

/-- If a nonnegative real period parameter is at most `30`, its first-repeat
entropy tax is at least `1 / 992`.  This is purely rational algebra. -/
theorem repeatTax_ge_heightOneGap
    (q : ℝ) (hq0 : 0 ≤ q) (hq30 : q ≤ 30) :
    heightOneGap ≤ 1 / ((q + 1) * (q + 2)) := by
  have hq1 : 0 < q + 1 := by linarith
  have hq2 : 0 < q + 2 := by linarith
  have hdenpos : 0 < (q + 1) * (q + 2) := mul_pos hq1 hq2
  have hfactor : 0 ≤ (30 - q) * (q + 33) :=
    mul_nonneg (sub_nonneg.mpr hq30) (by linarith)
  have hdenle : (q + 1) * (q + 2) ≤ 992 := by
    nlinarith
  rw [heightOneGap]
  apply (div_le_iff₀ hdenpos).2
  norm_num at hdenle ⊢
  nlinarith

/-- Terminal sporadic case: the B53 first-repeat lower bound and the table
bound `q ≤ 30` imply the uniform height-one threshold. -/
theorem sporadic_terminal_gap
    (C q : ℝ)
    (hq0 : 0 ≤ q) (hq30 : q ≤ 30)
    (hC : (1 : ℝ) / 2 + 1 / ((q + 1) * (q + 2)) ≤ C) :
    heightOneThreshold ≤ C := by
  have htax := repeatTax_ge_heightOneGap q hq0 hq30
  unfold heightOneThreshold
  linarith

/-- Terminal case split after Bober's classification and the three family
entropy estimates have been supplied. -/
theorem heightOne_classification_terminal_gap
    (C : ℝ)
    (hcases :
      Real.log 2 ≤ C ∨
      Real.log 3 / 2 ≤ C ∨
      heightOneThreshold ≤ C) :
    heightOneThreshold ≤ C := by
  rcases hcases with hlog2 | hlog3 | hsporadic
  · exact le_trans (le_of_lt heightOneThreshold_lt_log_two) hlog2
  · exact le_trans (le_of_lt heightOneThreshold_lt_half_log_three) hlog3
  · exact hsporadic

/-- Any individual datum below the uniform threshold is not of height one,
provided the source/classification bridge supplies the height-one lower bound. -/
theorem not_heightOne_of_below_threshold
    (height : ℕ) (C : ℝ)
    (hheightOne : height = 1 → heightOneThreshold ≤ C)
    (hC : C < heightOneThreshold) :
    height ≠ 1 := by
  intro hh
  exact (not_le_of_gt hC) (hheightOne hh)

/-- Sequence form: a positive-height family whose entropy eventually lies below
the uniform threshold must eventually have height at least two. -/
theorem eventually_height_at_least_two
    (height : ℕ → ℕ) (C : ℕ → ℝ)
    (hpositive : ∀ n, 1 ≤ height n)
    (hheightOne : ∀ n, height n = 1 → heightOneThreshold ≤ C n)
    (hbelow : ∀ᶠ n in Filter.atTop, C n < heightOneThreshold) :
    ∀ᶠ n in Filter.atTop, 2 ≤ height n := by
  filter_upwards [hbelow] with n hn
  have hne : height n ≠ 1 :=
    not_heightOne_of_below_threshold (height n) (C n) (hheightOne n) hn
  omega

/-- A target value at `1 / q` cannot occur before the first possible jump at
`1 / M`; hence the scale `q` is at most the largest coefficient `M`. -/
theorem targetScale_le_maxCoefficient
    (F : ℝ → ℤ) (M q : ℝ)
    (hM : 0 < M) (hq : 0 < q)
    (hzero : ∀ t : ℝ, 0 ≤ t → t < 1 / M → F t = 0)
    (htarget : F (1 / q) = 1) :
    q ≤ M := by
  by_contra hqM
  have hMq : M < q := lt_of_not_ge hqM
  have hlt : (1 : ℝ) / q < 1 / M := by
    rw [div_lt_div_iff₀ hq hM]
    linarith
  have hz := hzero (1 / q) (by positivity) hlt
  rw [htarget] at hz
  norm_num at hz

/-- In the second infinite family, when `a < 2b`, the matched `b`-half-grid
point lies strictly before twice the corresponding `a`-half-grid point. -/
theorem familyTwo_mappedZero_beforeDouble
    (a b α β : ℝ)
    (hb : 0 < b) (hskew : a < 2 * b) (hα : 0 < α)
    (hmap : b * β = a * α) :
    β < 2 * α := by
  have hmul : b * β < b * (2 * α) := by
    rw [hmap]
    have hpos : 0 < (2 * b - a) * α :=
      mul_pos (sub_pos.mpr hskew) hα
    nlinarith
  exact (mul_lt_mul_left hb).mp hmul

/-- A component ending before twice its left endpoint cannot contain a full
interval `[s, 2s]` beginning inside that component. -/
theorem shortComponent_blocks_dyadic
    (α β s : ℝ)
    (hαs : α ≤ s) (hsβ : 2 * s ≤ β) (hshort : β < 2 * α) :
    False := by
  linarith

/-- Combined real-geometric core of the `b > a / 2` obstruction in Bober's
second infinite family. -/
theorem familyTwo_skew_blocks_dyadic_component
    (a b α β s : ℝ)
    (hb : 0 < b) (hskew : a < 2 * b) (hα : 0 < α)
    (hmap : b * β = a * α)
    (hαs : α ≤ s) (hsβ : 2 * s ≤ β) :
    False := by
  exact shortComponent_blocks_dyadic α β s hαs hsβ
    (familyTwo_mappedZero_beforeDouble a b α β hb hskew hα hmap)

#print axioms heightOneThreshold_lt_log_two
#print axioms heightOneThreshold_lt_half_log_three
#print axioms repeatTax_ge_heightOneGap
#print axioms sporadic_terminal_gap
#print axioms heightOne_classification_terminal_gap
#print axioms not_heightOne_of_below_threshold
#print axioms eventually_height_at_least_two
#print axioms targetScale_le_maxCoefficient
#print axioms familyTwo_mappedZero_beforeDouble
#print axioms shortComponent_blocks_dyadic
#print axioms familyTwo_skew_blocks_dyadic_component

end RHB53
