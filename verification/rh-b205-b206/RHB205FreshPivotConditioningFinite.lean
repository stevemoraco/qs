import Mathlib

/-!
# RH B205 fresh-prime pivot conditioning firewall

Finite real algebra behind the B205 transporter audit.

Formalized here:
* a short root block `[a,a+h)` with `0<=h<=a` has square-span at most `3*a*h`;
* a fresh first-incidence coefficient `(n^2/p)-1`, with `a^2<p<=n^2`
  inside such a block, is at most `3*h/a`;
* if a total fresh-pivot coefficient obeys the cleared budget `a*K<=3*h^2`,
  then obtaining one-sided gain `gain` by a target scaling of squared size `s2`
  forces the metric product inequality `a*gain<=3*s2*h^2`.

These declarations do NOT formalize primes-as-primes, asymptotic subpower
notation, Zhao/B191, Deng--Yang--Lu, BGST, B200's RH equivalence, B46, zeta,
RH, or negation of RH.
-/

namespace RHB205FreshPivotConditioningFinite

theorem short_block_square_span
    {a h : ℝ}
    (ha : 0 ≤ a)
    (hh0 : 0 ≤ h)
    (hh : h ≤ a) :
    (a + h) ^ 2 - a ^ 2 ≤ 3 * a * h := by
  have haux : 0 ≤ h * (a - h) :=
    mul_nonneg hh0 (sub_nonneg.mpr hh)
  nlinarith

theorem fresh_point_coefficient_bound
    {a h p n : ℝ}
    (ha : 0 < a)
    (hh0 : 0 ≤ h)
    (hh : h ≤ a)
    (hn0 : 0 ≤ n)
    (hn : n ≤ a + h)
    (hp : a ^ 2 < p)
    (hpn : p ≤ n ^ 2) :
    a * (n ^ 2 / p - 1) ≤ 3 * h := by
  have hsum0 : 0 ≤ a + h := add_nonneg ha.le hh0
  have hplus : 0 ≤ a + h + n := by nlinarith
  have hminus : 0 ≤ a + h - n := sub_nonneg.mpr hn
  have hsquare : 0 ≤ (a + h - n) * (a + h + n) :=
    mul_nonneg hminus hplus
  have hspan : (a + h) ^ 2 - a ^ 2 ≤ 3 * a * h :=
    short_block_square_span ha.le hh0 hh
  have hnp : n ^ 2 - p ≤ 3 * a * h := by
    nlinarith
  have hp0 : 0 < p := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    linarith
  have hcleared : a * (n ^ 2 - p) ≤ 3 * h * p := by
    have hleft : a * (n ^ 2 - p) ≤ 3 * a ^ 2 * h := by
      nlinarith
    have hright : 3 * a ^ 2 * h ≤ 3 * p * h := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg (by norm_num) hh0)
    nlinarith
  calc
    a * (n ^ 2 / p - 1) = (a * (n ^ 2 - p)) / p := by
      field_simp [ne_of_gt hp0]
      <;> ring
    _ ≤ 3 * h := (div_le_iff₀ hp0).2 (by nlinarith [hcleared])

theorem pivot_gain_forces_metric_product
    {a h K gain s2 : ℝ}
    (ha : 0 ≤ a)
    (hs2 : 0 ≤ s2)
    (hK : a * K ≤ 3 * h ^ 2)
    (htransport : gain ≤ s2 * K) :
    a * gain ≤ 3 * s2 * h ^ 2 := by
  calc
    a * gain ≤ a * (s2 * K) :=
      mul_le_mul_of_nonneg_left htransport ha
    _ = s2 * (a * K) := by ring
    _ ≤ s2 * (3 * h ^ 2) :=
      mul_le_mul_of_nonneg_left hK hs2
    _ = 3 * s2 * h ^ 2 := by ring

theorem exact_pivot_scaling_identity
    {a h : ℝ}
    (ha : a ≠ 0)
    (hh : h ≠ 0) :
    (a / (3 * h ^ 2)) * (3 * h ^ 2 / a) = 1 := by
  field_simp [ha, hh]

#print axioms short_block_square_span
#print axioms fresh_point_coefficient_bound
#print axioms pivot_gain_forces_metric_product
#print axioms exact_pivot_scaling_identity

end RHB205FreshPivotConditioningFinite
