import Mathlib

namespace SixLaneAudit.RHPrimePrefixGapTax

/-- Exact square-root AM--GM defect. -/
theorem sqrt_gap_identity {x theta : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta) :
    Real.sqrt x + theta / Real.sqrt x - 2 * Real.sqrt theta =
      (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  have hsx_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsx_ne : Real.sqrt x ≠ 0 := ne_of_gt hsx_pos
  have hsx_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx)
  have hst_sq : (Real.sqrt theta) ^ 2 = theta := by
    simpa using Real.sq_sqrt htheta
  field_simp [hsx_ne]
  nlinarith

/-- The endpoint tax is nonnegative. -/
theorem sqrt_gap_nonneg {x theta : ℝ}
    (hx : 0 < x) :
    0 ≤ (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  exact div_nonneg (sq_nonneg _) (le_of_lt (Real.sqrt_pos.2 hx))

/-- Continuous margin minus prime-prefix statistic equals the endpoint tax. -/
theorem margin_sub_prefix_eq_tax
    {x theta baseline margin prefix : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta)
    (hmargin : margin = Real.sqrt x + theta / Real.sqrt x - baseline)
    (hprefix : prefix = 2 * Real.sqrt theta - baseline) :
    margin - prefix =
      (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  calc
    margin - prefix =
        Real.sqrt x + theta / Real.sqrt x - 2 * Real.sqrt theta := by
          rw [hmargin, hprefix]
          ring
    _ = (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x :=
      sqrt_gap_identity hx htheta

/-- Prime-prefix value never exceeds the continuous margin. -/
theorem prefix_le_margin
    {x theta baseline margin prefix : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta)
    (hmargin : margin = Real.sqrt x + theta / Real.sqrt x - baseline)
    (hprefix : prefix = 2 * Real.sqrt theta - baseline) :
    prefix ≤ margin := by
  have htax := sqrt_gap_nonneg (theta := theta) hx
  have hid := margin_sub_prefix_eq_tax hx htheta hmargin hprefix
  linarith

/-- If `I = -2 margin`, prefix positivity is exactly the tax-beating gate. -/
theorem prefix_pos_iff_integral_beats_tax
    {I margin prefix tax : ℝ}
    (hI : I = -2 * margin)
    (htax : margin - prefix = tax) :
    0 < prefix ↔ 2 * tax < -I := by
  constructor <;> intro h <;> nlinarith

/-- Fully substituted critical-integral gate. -/
theorem prefix_pos_iff_critical_integral_gap
    {x theta baseline margin prefix I : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta)
    (hmargin : margin = Real.sqrt x + theta / Real.sqrt x - baseline)
    (hprefix : prefix = 2 * Real.sqrt theta - baseline)
    (hI : I = -2 * margin) :
    0 < prefix ↔
      2 * ((Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x) < -I := by
  apply prefix_pos_iff_integral_beats_tax hI
  exact margin_sub_prefix_eq_tax hx htheta hmargin hprefix

#print axioms sqrt_gap_identity
#print axioms sqrt_gap_nonneg
#print axioms margin_sub_prefix_eq_tax
#print axioms prefix_le_margin
#print axioms prefix_pos_iff_integral_beats_tax
#print axioms prefix_pos_iff_critical_integral_gap

end SixLaneAudit.RHPrimePrefixGapTax
