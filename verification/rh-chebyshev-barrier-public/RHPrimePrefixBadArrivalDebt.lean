import Mathlib

namespace RHPrimePrefixBadArrivalDebt

/-- Positive part of a real scalar. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Negative-part magnitude of a real scalar. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

/-- Every real scalar is its positive part minus its negative-part magnitude. -/
theorem value_eq_posPart_sub_negPart (x : ℝ) :
    x = posPart x - negPart x := by
  by_cases hx : 0 ≤ x
  · simp [posPart, negPart, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hnx : 0 ≤ -x := neg_nonneg.mpr hx'
    simp [posPart, negPart, max_eq_right hx', max_eq_left hnx]

/-- Finite signed reserve decomposition into favorable arrivals and debt. -/
theorem sum_eq_posPart_sum_sub_negPart_sum (xs : List ℝ) :
    xs.sum = (xs.map posPart).sum - (xs.map negPart).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [List.sum_cons, List.sum_cons, ih, value_eq_posPart_sub_negPart]
      ring

/-- The cumulative bad-arrival debt is nonnegative. -/
theorem negPart_sum_nonneg (xs : List ℝ) :
    0 ≤ (xs.map negPart).sum := by
  exact List.sum_nonneg fun x hx => by simp [negPart]

/-- Root-coordinate version of the pointwise debt bound.

Interpret `a=sqrt(theta(q))`, `b=sqrt(theta(q^-))`, `s=sqrt(q)`,
`w=log q`, and `debt=[-Delta F(q)]_+`. On a genuinely adverse arrival,
`a>s`. The theorem proves

`debt ≤ w (theta(q)-q) / (2 q^(3/2))`.
-/
theorem adverse_debt_le_chebyshev_excess
    {a b s w debt : ℝ}
    (hs : 0 < s)
    (hb : 0 ≤ b)
    (hba : b < a)
    (hsa : s ≤ a)
    (hw : w = a ^ 2 - b ^ 2)
    (hdebt : debt = w / s - 2 * (a - b)) :
    debt ≤ w * (a ^ 2 - s ^ 2) / (2 * s ^ 3) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hab : 0 < a - b := sub_pos.mpr hba
  have habsum : 0 < a + b := by nlinarith
  have hwpos : 0 < w := by
    rw [hw]
    calc
      0 < (a - b) * (a + b) := mul_pos hab habsum
      _ = a ^ 2 - b ^ 2 := by ring
  have hfrac : 1 / a ≤ 2 / (a + b) := by
    apply (div_le_div_iff₀ ha habsum).2
    nlinarith
  have hmul : w / a ≤ 2 * w / (a + b) := by
    have h := mul_le_mul_of_nonneg_left hfrac (le_of_lt hwpos)
    field_simp [ne_of_gt ha, ne_of_gt habsum] at h ⊢
    nlinarith
  have hrewrite : 2 * (a - b) = 2 * w / (a + b) := by
    rw [hw]
    field_simp [ne_of_gt habsum]
    ring
  have hfirst : debt ≤ w / s - w / a := by
    rw [hdebt, hrewrite]
    linarith
  have hnonneg : 0 ≤ a - s := sub_nonneg.mpr hsa
  have haux : 0 ≤ a * (a + s) - 2 * s ^ 2 := by
    have hfactor : a * (a + s) - 2 * s ^ 2 = (a - s) * (a + 2 * s) := by ring
    rw [hfactor]
    exact mul_nonneg hnonneg (by nlinarith [le_of_lt ha, le_of_lt hs])
  have hpoly : 2 * s ^ 2 * (a - s) ≤ a * (a ^ 2 - s ^ 2) := by
    have hprod : 0 ≤ (a - s) * (a * (a + s) - 2 * s ^ 2) :=
      mul_nonneg hnonneg haux
    nlinarith
  have hden1 : 0 < a * s := mul_pos ha hs
  have hden2 : 0 < 2 * s ^ 3 := by positivity
  have hscalar : (a - s) / (a * s) ≤ (a ^ 2 - s ^ 2) / (2 * s ^ 3) := by
    apply (div_le_div_iff₀ hden1 hden2).2
    nlinarith [hpoly]
  have hmul2 := mul_le_mul_of_nonneg_left hscalar (le_of_lt hwpos)
  have hid : w / s - w / a = w * ((a - s) / (a * s)) := by
    field_simp [ne_of_gt ha, ne_of_gt hs]
    ring
  rw [hid] at hfirst
  exact hfirst.trans hmul2

/-- A negative terminal reserve is bounded by cumulative debt once favorable
arrivals are discarded. -/
theorem terminal_negative_part_le_debt
    {F0 good debt F : ℝ}
    (hF0 : 0 ≤ F0)
    (hgood : 0 ≤ good)
    (hledger : F = F0 + good - debt) :
    negPart F ≤ debt := by
  by_cases hF : 0 ≤ F
  · simp [negPart, max_eq_right (neg_nonpos.mpr hF)]
    have : 0 ≤ debt := by linarith
    exact this
  · have hF' : F ≤ 0 := le_of_not_ge hF
    have hneg : negPart F = -F := by simp [negPart, max_eq_left (neg_nonneg.mpr hF')]
    rw [hneg, hledger]
    linarith

#print axioms value_eq_posPart_sub_negPart
#print axioms sum_eq_posPart_sum_sub_negPart_sum
#print axioms negPart_sum_nonneg
#print axioms adverse_debt_le_chebyshev_excess
#print axioms terminal_negative_part_le_debt

end RHPrimePrefixBadArrivalDebt
