import Millennium.YangMills.RGCubicLocalResidual

/-!
# Quartic perturbation stability for the two-loop RG coordinate

This file closes the finite scalar perturbation step left open by
`RGCubicLocalResidual.lean`.

For the exact cubic step

    w = u * (1 + b*u + c*u^2)

and a perturbed step `v = w + r` with `|r| <= R*u^4`, the same corrected
coordinate

    Phi(u) = 1/(b*u) + (c/b^2 - 1) * log u

changes by only `O(u^2)` provided the perturbation is small enough to keep
`v` uniformly positive. The file also proves that the quadratic growth needed
by `RGAccumulatedRemainder.lean` survives.

Honesty boundary: these are finite real-variable estimates. They do not prove
that an actual Yang--Mills blocking map has a regulator/volume/boundary-uniform
`O(u^4)` remainder, do not identify a lattice coupling with a canonical
continuum scheme, and do not prove a physical mass gap or OS reconstruction.
-/

namespace Millennium.YangMills

/-- If two positive arguments are both bounded below at scale `u`, their
logarithms are Lipschitz with the explicit coarse constant `2/u`. -/
theorem abs_log_sub_log_le_two_mul_abs_sub_div
    (u v w : ℝ)
    (hu : 0 < u) (hw : u ≤ w) (hv : u / 2 ≤ v) :
    |Real.log v - Real.log w| ≤ 2 * |v - w| / u := by
  have hwpos : 0 < w := lt_of_lt_of_le hu hw
  have hvpos : 0 < v := by linarith
  rcases le_total w v with hwv | hvw
  · have hlog_nonneg : 0 ≤ Real.log v - Real.log w := by
      exact sub_nonneg.mpr (Real.log_le_log hwpos hwv)
    rw [abs_of_nonneg hlog_nonneg]
    have hratio : 0 < v / w := div_pos hvpos hwpos
    have hlog : Real.log v - Real.log w ≤ v / w - 1 := by
      rw [← Real.log_div hvpos.ne' hwpos.ne']
      exact Real.log_le_sub_one_of_pos hratio
    have hfrac : v / w - 1 = (v - w) / w := by
      field_simp [hwpos.ne']
      ring
    have hdiff : 0 ≤ v - w := sub_nonneg.mpr hwv
    have hdiv : (v - w) / w ≤ (v - w) / u := by
      exact div_le_div_of_nonneg_left hdiff hu hw
    have habs : |v - w| = v - w := abs_of_nonneg hdiff
    rw [hfrac] at hlog
    rw [habs]
    have hnonneg : 0 ≤ (v - w) / u := div_nonneg hdiff (le_of_lt hu)
    nlinarith
  · have hlog_nonneg : 0 ≤ Real.log w - Real.log v := by
      exact sub_nonneg.mpr (Real.log_le_log hvpos hvw)
    have habslog : |Real.log v - Real.log w| = Real.log w - Real.log v := by
      rw [abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (Real.log_le_log hvpos hvw)
    rw [habslog]
    have hratio : 0 < w / v := div_pos hwpos hvpos
    have hlog : Real.log w - Real.log v ≤ w / v - 1 := by
      rw [← Real.log_div hwpos.ne' hvpos.ne']
      exact Real.log_le_sub_one_of_pos hratio
    have hfrac : w / v - 1 = (w - v) / v := by
      field_simp [hvpos.ne']
      ring
    have hdiff : 0 ≤ w - v := sub_nonneg.mpr hvw
    have hvhalfpos : 0 < u / 2 := half_pos hu
    have hdiv : (w - v) / v ≤ (w - v) / (u / 2) := by
      exact div_le_div_of_nonneg_left hdiff hvhalfpos hv
    have habs : |v - w| = w - v := by
      rw [abs_of_nonpos (sub_nonpos.mpr hvw)]
      ring
    rw [hfrac] at hlog
    rw [habs]
    have hrewrite : (w - v) / (u / 2) = 2 * (w - v) / u := by
      field_simp [hu.ne']
      ring
    rw [hrewrite] at hdiv
    exact le_trans hlog hdiv

/-- A quartic perturbation small on a fixed weak-coupling interval cannot push
the cubic step below half the incoming coupling. -/
theorem quartic_perturbation_keeps_half_lower_bound
    (b c u U R r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U)
    (hR : 0 ≤ R) (hr : |r| ≤ R * u^4)
    (hsmall : R * U^3 ≤ 1 / 2) :
    u / 2 ≤ cubicRGStep b c u + r := by
  have hU : 0 < U := lt_of_lt_of_le hu huU
  have hstep : u ≤ cubicRGStep b c u := by
    unfold cubicRGStep
    have hnonneg : 0 ≤ b * u + c * u^2 := by positivity
    nlinarith
  have hu3 : u^3 ≤ U^3 := by
    exact pow_le_pow_left₀ (le_of_lt hu) huU 3
  have hRu3 : R * u^3 ≤ 1 / 2 := by
    calc
      R * u^3 ≤ R * U^3 := mul_le_mul_of_nonneg_left hu3 hR
      _ ≤ 1 / 2 := hsmall
  have hquartic : R * u^4 ≤ u / 2 := by
    have hu0 : 0 ≤ u := le_of_lt hu
    have hid : R * u^4 = (R * u^3) * u := by ring
    rw [hid]
    nlinarith
  have hr_lower : -R * u^4 ≤ r := by
    have := neg_le_of_abs_le hr
    nlinarith
  nlinarith

/-- The reciprocal part of the corrected coordinate changes by `O(u^2)` under
an `O(u^4)` perturbation. -/
theorem quartic_perturbation_reciprocal_le_quadratic
    (b c u U R r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U)
    (hR : 0 ≤ R) (hr : |r| ≤ R * u^4)
    (hsmall : R * U^3 ≤ 1 / 2) :
    |1 / (b * (cubicRGStep b c u + r)) -
        1 / (b * cubicRGStep b c u)|
      ≤ (2 * R / b) * u^2 := by
  let w : ℝ := cubicRGStep b c u
  let v : ℝ := w + r
  have hw : u ≤ w := by
    dsimp [w]
    unfold cubicRGStep
    have hnonneg : 0 ≤ b * u + c * u^2 := by positivity
    nlinarith
  have hvhalf : u / 2 ≤ v := by
    dsimp [v, w]
    exact quartic_perturbation_keeps_half_lower_bound b c u U R r hb hc hu huU hR hr hsmall
  have hwpos : 0 < w := lt_of_lt_of_le hu hw
  have hvpos : 0 < v := by linarith
  have hvwprod : u^2 / 2 ≤ v * w := by
    have hu0 : 0 ≤ u := le_of_lt hu
    nlinarith [mul_le_mul hvhalf hw (by positivity : 0 ≤ u / 2) (by positivity : 0 ≤ w)]
  have hprodpos : 0 < v * w := mul_pos hvpos hwpos
  have hdiff : |v - w| = |r| := by
    dsimp [v]
    ring_nf
  have hfrac_identity :
      1 / (b * v) - 1 / (b * w) = (w - v) / (b * v * w) := by
    field_simp [hb.ne', hvpos.ne', hwpos.ne']
    ring
  rw [hfrac_identity, abs_div, abs_mul, abs_mul]
  have hbabs : |b| = b := abs_of_pos hb
  have hvabs : |v| = v := abs_of_pos hvpos
  have hwabs : |w| = w := abs_of_pos hwpos
  rw [hbabs, hvabs, hwabs]
  have hnum : |w - v| = |r| := by
    rw [abs_sub_comm]
    exact hdiff
  rw [hnum]
  have hden : 0 < b * v * w := by positivity
  rw [div_le_iff₀ hden]
  have hr' : |r| ≤ R * u^4 := hr
  have htarget_nonneg : 0 ≤ (2 * R / b) * u^2 := by positivity
  have hb0 : 0 ≤ b := le_of_lt hb
  have hR0 : 0 ≤ R := hR
  have hu0 : 0 ≤ u := le_of_lt hu
  have hmul := mul_le_mul_of_nonneg_left hvwprod hb0
  nlinarith [sq_nonneg u]

/-- The logarithmic part of the corrected coordinate changes by `O(u^3)`,
hence by `O(u^2)` on a fixed interval. -/
theorem quartic_perturbation_log_le_quadratic
    (b c u U R r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U)
    (hR : 0 ≤ R) (hr : |r| ≤ R * u^4)
    (hsmall : R * U^3 ≤ 1 / 2) :
    |Real.log (cubicRGStep b c u + r) -
        Real.log (cubicRGStep b c u)|
      ≤ (2 * R * U) * u^2 := by
  let w : ℝ := cubicRGStep b c u
  let v : ℝ := w + r
  have hw : u ≤ w := by
    dsimp [w]
    unfold cubicRGStep
    have hnonneg : 0 ≤ b * u + c * u^2 := by positivity
    nlinarith
  have hvhalf : u / 2 ≤ v := by
    dsimp [v, w]
    exact quartic_perturbation_keeps_half_lower_bound b c u U R r hb hc hu huU hR hr hsmall
  have hlog := abs_log_sub_log_le_two_mul_abs_sub_div u v w hu hw hvhalf
  have hdiff : |v - w| = |r| := by
    dsimp [v]
    ring_nf
  rw [hdiff] at hlog
  have hru : |r| / u ≤ R * u^3 := by
    rw [div_le_iff₀ hu]
    have hr' := hr
    nlinarith [sq_nonneg u]
  have huU' : u^3 ≤ U * u^2 := by
    have hu0 : 0 ≤ u := le_of_lt hu
    nlinarith [sq_nonneg u]
  calc
    |Real.log (cubicRGStep b c u + r) - Real.log (cubicRGStep b c u)|
        = |Real.log v - Real.log w| := by rfl
    _ ≤ 2 * |r| / u := hlog
    _ ≤ 2 * (R * u^3) := by nlinarith
    _ ≤ (2 * R * U) * u^2 := by nlinarith

/-- Main perturbation theorem: an `O(u^4)` error preserves the local `O(u^2)`
residual of the two-loop corrected coordinate. -/
theorem cubic_corrected_coordinate_quartic_perturbation_le_quadratic
    (b c u U R r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U)
    (hR : 0 ≤ R) (hr : |r| ≤ R * u^4)
    (hsmall : R * U^3 ≤ 1 / 2) :
    |cubicCorrectedCoordinate b c (cubicRGStep b c u + r) -
        cubicCorrectedCoordinate b c (cubicRGStep b c u)|
      ≤ 2 * R * (1 / b + |c / b^2 - 1| * U) * u^2 := by
  have hrec := quartic_perturbation_reciprocal_le_quadratic
    b c u U R r hb hc hu huU hR hr hsmall
  have hlog := quartic_perturbation_log_le_quadratic
    b c u U R r hb hc hu huU hR hr hsmall
  unfold cubicCorrectedCoordinate
  have hsplit :
      1 / (b * (cubicRGStep b c u + r)) +
          (c / b^2 - 1) * Real.log (cubicRGStep b c u + r) -
        (1 / (b * cubicRGStep b c u) +
          (c / b^2 - 1) * Real.log (cubicRGStep b c u))
      = (1 / (b * (cubicRGStep b c u + r)) -
          1 / (b * cubicRGStep b c u))
        + (c / b^2 - 1) *
          (Real.log (cubicRGStep b c u + r) -
            Real.log (cubicRGStep b c u)) := by ring
  rw [hsplit]
  calc
    |(1 / (b * (cubicRGStep b c u + r)) -
          1 / (b * cubicRGStep b c u))
        + (c / b^2 - 1) *
          (Real.log (cubicRGStep b c u + r) -
            Real.log (cubicRGStep b c u))|
      ≤ |1 / (b * (cubicRGStep b c u + r)) -
          1 / (b * cubicRGStep b c u)|
        + |c / b^2 - 1| *
          |Real.log (cubicRGStep b c u + r) -
            Real.log (cubicRGStep b c u)| := by
          calc
            _ ≤ |1 / (b * (cubicRGStep b c u + r)) -
                  1 / (b * cubicRGStep b c u)|
                + |(c / b^2 - 1) *
                    (Real.log (cubicRGStep b c u + r) -
                      Real.log (cubicRGStep b c u))| := abs_add_le _ _
            _ = _ := by rw [abs_mul]
    _ ≤ (2 * R / b) * u^2 +
        |c / b^2 - 1| * ((2 * R * U) * u^2) := by
          exact add_le_add hrec
            (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
    _ = 2 * R * (1 / b + |c / b^2 - 1| * U) * u^2 := by
          field_simp [hb.ne']
          ring

/-- Quartic perturbations preserve a definite quadratic increase if their
coefficient is small relative to the quadratic RG coefficient. -/
theorem quartic_perturbation_preserves_quadratic_growth
    (b c u U R r : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c)
    (hu : 0 < u) (huU : u ≤ U)
    (hR : 0 ≤ R) (hr : |r| ≤ R * u^4)
    (hgrowth : R * U^2 ≤ b / 2) :
    (b / 2) * u^2 ≤ cubicRGStep b c u + r - u := by
  have hU : 0 < U := lt_of_lt_of_le hu huU
  have hu2 : u^2 ≤ U^2 := by
    exact pow_le_pow_left₀ (le_of_lt hu) huU 2
  have hRu2 : R * u^2 ≤ b / 2 := by
    calc
      R * u^2 ≤ R * U^2 := mul_le_mul_of_nonneg_left hu2 hR
      _ ≤ b / 2 := hgrowth
  have hr_lower : -R * u^4 ≤ r := by
    have := neg_le_of_abs_le hr
    nlinarith
  unfold cubicRGStep
  have hcu3 : 0 ≤ c * u^3 := by positivity
  nlinarith [sq_nonneg u]

#print axioms abs_log_sub_log_le_two_mul_abs_sub_div
#print axioms quartic_perturbation_keeps_half_lower_bound
#print axioms quartic_perturbation_reciprocal_le_quadratic
#print axioms quartic_perturbation_log_le_quadratic
#print axioms cubic_corrected_coordinate_quartic_perturbation_le_quadratic
#print axioms quartic_perturbation_preserves_quadratic_growth

end Millennium.YangMills
