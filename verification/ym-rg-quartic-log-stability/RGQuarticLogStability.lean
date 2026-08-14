import Mathlib

/-!
# Corrected-coordinate stability under a quartic RG perturbation

This file closes the finite real-analysis estimate needed to make the
previous two-loop corrected-coordinate argument robust under an `O(u^4)`
one-step error.

If `w >= u > 0`, `v >= u/2`, `v = w + r`, and `|r| <= R u^4`, then

    |log v - log w| <= 2 R u^3.

For the generic corrected coordinate

    Phi(x) = 1/(b*x) + p*log x,

the same hypotheses, with `u <= U`, give

    |Phi(v)-Phi(w)|
      <= (2R/b + 2|p| R U) u^2.

Thus a genuine fourth-order recurrence error contributes only `O(u^2)` to
the compensated inverse-coupling clock, exactly the summable order required
by the previously banked crossing-time theorem.

Honesty boundary: these are finite real-analysis theorems. They do not prove
that a four-dimensional Yang--Mills RG map has a uniform quartic remainder,
do not identify a renormalization scheme, and do not prove a mass gap or
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

/-- Generic compensated inverse-coupling coordinate.  In the cubic two-loop
model one later substitutes `p = c/b^2 - 1`. -/
noncomputable def quarticCorrectedCoordinate (b p x : ℝ) : ℝ :=
  1 / (b * x) + p * Real.log x

/-- A fourth-order perturbation changes the full corrected coordinate by only
`O(u^2)` on a fixed weak-coupling interval. -/
theorem corrected_coordinate_difference_le_quartic
    (b p u U v w r R : ℝ)
    (hb : 0 < b)
    (hu : 0 < u)
    (huU : u ≤ U)
    (hw : u ≤ w)
    (hv : u / 2 ≤ v)
    (hvw : v = w + r)
    (hR : 0 ≤ R)
    (hr : |r| ≤ R * u^4) :
    |quarticCorrectedCoordinate b p v - quarticCorrectedCoordinate b p w|
      ≤ (2 * R / b + 2 * |p| * R * U) * u^2 := by
  have hwpos : 0 < w := lt_of_lt_of_le hu hw
  have hu2pos : 0 < u / 2 := by positivity
  have hvpos : 0 < v := lt_of_lt_of_le hu2pos hv
  have hprod : u^2 / 2 ≤ v * w := by
    calc
      u^2 / 2 = (u / 2) * u := by ring
      _ ≤ v * u := mul_le_mul_of_nonneg_right hv (le_of_lt hu)
      _ ≤ v * w := mul_le_mul_of_nonneg_left hw (le_of_lt hvpos)
  have hcoef : 0 ≤ 2 * R * u^2 := by positivity
  have hscaleProd : R * u^4 ≤ 2 * R * u^2 * (v * w) := by
    calc
      R * u^4 = (2 * R * u^2) * (u^2 / 2) := by ring
      _ ≤ (2 * R * u^2) * (v * w) :=
        mul_le_mul_of_nonneg_left hprod hcoef
      _ = 2 * R * u^2 * (v * w) := by ring
  have hrecId :
      1 / (b * v) - 1 / (b * w) = -r / (b * v * w) := by
    field_simp [ne_of_gt hb, ne_of_gt hvpos, ne_of_gt hwpos]
    nlinarith [hvw]
  have hden : 0 < b * v * w := by positivity
  have hrec :
      |1 / (b * v) - 1 / (b * w)| ≤ (2 * R / b) * u^2 := by
    rw [hrecId, abs_div, abs_neg, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |r| ≤ R * u^4 := hr
      _ ≤ 2 * R * u^2 * (v * w) := hscaleProd
      _ = ((2 * R / b) * u^2) * (b * v * w) := by
        field_simp [ne_of_gt hb]
        ring
  have hlog := log_difference_le_two_quartic u v w r R hu hw hv hvw hR hr
  have hscaleLog : 2 * R * u^3 ≤ 2 * R * U * u^2 := by
    have hnon : 0 ≤ 2 * R * u^2 := by positivity
    calc
      2 * R * u^3 = (2 * R * u^2) * u := by ring
      _ ≤ (2 * R * u^2) * U := mul_le_mul_of_nonneg_left huU hnon
      _ = 2 * R * U * u^2 := by ring
  have hpLog :
      |p * (Real.log v - Real.log w)| ≤ 2 * |p| * R * U * u^2 := by
    rw [abs_mul]
    calc
      |p| * |Real.log v - Real.log w|
          ≤ |p| * (2 * R * U * u^2) :=
            mul_le_mul_of_nonneg_left (le_trans hlog hscaleLog) (abs_nonneg p)
      _ = 2 * |p| * R * U * u^2 := by ring
  have hdecomp :
      quarticCorrectedCoordinate b p v - quarticCorrectedCoordinate b p w =
        (1 / (b * v) - 1 / (b * w)) +
          p * (Real.log v - Real.log w) := by
    unfold quarticCorrectedCoordinate
    ring
  rw [hdecomp]
  calc
    |(1 / (b * v) - 1 / (b * w)) + p * (Real.log v - Real.log w)|
        ≤ |1 / (b * v) - 1 / (b * w)| +
            |p * (Real.log v - Real.log w)| := abs_add_le _ _
    _ ≤ (2 * R / b) * u^2 + 2 * |p| * R * U * u^2 :=
      add_le_add hrec hpLog
    _ = (2 * R / b + 2 * |p| * R * U) * u^2 := by ring

#print axioms log_difference_le_two_quartic
#print axioms corrected_coordinate_difference_le_quartic

end Millennium.YangMills
