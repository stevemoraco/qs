import Mathlib

/-!
# Logarithmic stability under a quartic RG perturbation

This file closes the logarithmic Lipschitz estimate needed to make the
previous two-loop corrected-coordinate argument robust under an `O(u^4)`
one-step error.

If `w >= u > 0`, `v >= u/2`, `v = w + r`, and `|r| <= R u^4`, then

    |log v - log w| <= 2 R u^3.

The proof uses only the elementary inequality `log x <= x - 1` twice, once
for `v/w` and once for `w/v`.  It is deliberately independent of any
Yang--Mills-specific blocking construction.

Honesty boundary: this is a finite real-analysis theorem.  It does not prove
that a four-dimensional Yang--Mills RG map has a uniform quartic remainder,
does not identify a renormalization scheme, and does not prove a mass gap or
Osterwalder--Schrader reconstruction.
-/

namespace Millennium.YangMills

/-- A quartic perturbation changes the logarithm by at most `2 R u^3` once
both the exact and perturbed steps stay uniformly above the input scale. -/
theorem log_difference_le_two_quartic
    (u v w r R : ℝ)
    (hu : 0 < u)
    (hw : u ≤ w)
    (hv : u / 2 ≤ v)
    (hvw : v = w + r)
    (hR : 0 ≤ R)
    (hr : |r| ≤ R * u^4) :
    |Real.log v - Real.log w| ≤ 2 * R * u^3 := by
  have hwpos : 0 < w := lt_of_lt_of_le hu hw
  have hu2pos : 0 < u / 2 := by positivity
  have hvpos : 0 < v := lt_of_lt_of_le hu2pos hv
  have hu3 : 0 ≤ u^3 := by positivity
  have hRu3 : 0 ≤ R * u^3 := mul_nonneg hR hu3
  have hru : r ≤ R * u^4 := le_trans (le_abs_self r) hr
  have hnru : -r ≤ R * u^4 := le_trans (neg_le_abs r) hr
  have hscaleW : R * u^4 ≤ R * u^3 * w := by
    calc
      R * u^4 = (R * u^3) * u := by ring
      _ ≤ (R * u^3) * w := mul_le_mul_of_nonneg_left hw hRu3
      _ = R * u^3 * w := by ring
  have huv : u ≤ 2 * v := by
    nlinarith [hv]
  have hscaleV : R * u^4 ≤ 2 * R * u^3 * v := by
    calc
      R * u^4 = (R * u^3) * u := by ring
      _ ≤ (R * u^3) * (2 * v) :=
        mul_le_mul_of_nonneg_left huv hRu3
      _ = 2 * R * u^3 * v := by ring
  have hrW : r ≤ R * u^3 * w := le_trans hru hscaleW
  have hnrV : -r ≤ 2 * R * u^3 * v := le_trans hnru hscaleV
  have hfracVW : v / w - 1 ≤ R * u^3 := by
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hwpos).2
    rw [hvw]
    nlinarith [hrW]
  have hw_eq : w = v - r := by
    linarith [hvw]
  have hfracWV : w / v - 1 ≤ 2 * R * u^3 := by
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hvpos).2
    rw [hw_eq]
    nlinarith [hnrV]
  have hlogVW := Real.log_le_sub_one_of_pos (div_pos hvpos hwpos)
  rw [Real.log_div (ne_of_gt hvpos) (ne_of_gt hwpos)] at hlogVW
  have hlogWV := Real.log_le_sub_one_of_pos (div_pos hwpos hvpos)
  rw [Real.log_div (ne_of_gt hwpos) (ne_of_gt hvpos)] at hlogWV
  have hup : Real.log v - Real.log w ≤ R * u^3 :=
    le_trans hlogVW hfracVW
  have hdown : Real.log w - Real.log v ≤ 2 * R * u^3 :=
    le_trans hlogWV hfracWV
  have hmono : R * u^3 ≤ 2 * R * u^3 := by
    nlinarith [hRu3]
  rw [abs_le]
  constructor
  · linarith [hdown]
  · exact le_trans hup hmono

#print axioms log_difference_le_two_quartic

end Millennium.YangMills
