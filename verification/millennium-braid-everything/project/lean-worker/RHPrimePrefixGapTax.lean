import Mathlib

/-!
# RH prime-prefix critical-integral gap tax

This file formalizes the finite real-algebra core of the prime-prefix
criterion banked in `stevemoraco/RH` PR #95.  It does **not** formalize the
Riemann hypothesis, the Chebyshev function, Johnston's weighted-integral
theorem, or the explicit formula.

The key identity is exact.  If

* `margin = sqrt x + theta / sqrt x - baseline`, and
* `prefix = 2 sqrt theta - baseline`,

then

`margin - prefix = (sqrt x - sqrt theta)^2 / sqrt x`.

If an analytic bridge additionally identifies a weighted Chebyshev integral
`I` by `I = -2 * margin`, then the prefix is positive exactly when

`2 * tax < -I`.

Thus mere negativity of `I` is insufficient: the integral must pay the
nonnegative endpoint gap tax.
-/

namespace RHPrimePrefixGapTax

/-- Exact square-root AM--GM defect, with every denominator hypothesis
explicit. -/
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

/-- The square-root tax is nonnegative. -/
theorem sqrt_gap_nonneg {x theta : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta) :
    0 ≤ (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  exact div_nonneg (sq_nonneg _) (le_of_lt (Real.sqrt_pos.2 hx))

/-- Exact decomposition of a continuous Chebyshev margin into the
prime-prefix statistic plus the endpoint tax.  `baseline` abstracts the
common term `sqrt 2 + A(x)`. -/
theorem margin_sub_prefix_eq_tax
    {x theta baseline margin prefix : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta)
    (hmargin :
      margin = Real.sqrt x + theta / Real.sqrt x - baseline)
    (hprefix :
      prefix = 2 * Real.sqrt theta - baseline) :
    margin - prefix =
      (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x := by
  calc
    margin - prefix =
        Real.sqrt x + theta / Real.sqrt x - 2 * Real.sqrt theta := by
          rw [hmargin, hprefix]
          ring
    _ = (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x :=
      sqrt_gap_identity hx htheta

/-- Prime-prefix value never exceeds the corresponding continuous margin. -/
theorem prefix_le_margin
    {x theta baseline margin prefix : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta)
    (hmargin :
      margin = Real.sqrt x + theta / Real.sqrt x - baseline)
    (hprefix :
      prefix = 2 * Real.sqrt theta - baseline) :
    prefix ≤ margin := by
  have htax := sqrt_gap_nonneg hx htheta
  have hid := margin_sub_prefix_eq_tax hx htheta hmargin hprefix
  linarith

/-- Abstract exact endgame.  If `I = -2 margin` and
`margin - prefix = tax`, then prefix positivity is equivalent to the
weighted integral beating twice the tax. -/
theorem prefix_pos_iff_integral_beats_tax
    {I margin prefix tax : ℝ}
    (hI : I = -2 * margin)
    (htax : margin - prefix = tax) :
    0 < prefix ↔ 2 * tax < -I := by
  constructor <;> intro h <;> nlinarith

/-- Fully substituted form of the critical-integral tax gate. -/
theorem prefix_pos_iff_critical_integral_gap
    {x theta baseline margin prefix I : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta)
    (hmargin :
      margin = Real.sqrt x + theta / Real.sqrt x - baseline)
    (hprefix :
      prefix = 2 * Real.sqrt theta - baseline)
    (hI : I = -2 * margin) :
    0 < prefix ↔
      2 * ((Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x) < -I := by
  apply prefix_pos_iff_integral_beats_tax hI
  exact margin_sub_prefix_eq_tax hx htheta hmargin hprefix

/-- A convenient upper bound for the tax using the unsquared discrepancy.
The exact denominator is at least `x^(3/2)` after rationalization. -/
theorem sqrt_gap_tax_le_discrepancy_square
    {x theta : ℝ}
    (hx : 0 < x) (htheta : 0 ≤ theta) :
    (Real.sqrt x - Real.sqrt theta) ^ 2 / Real.sqrt x ≤
      (x - theta) ^ 2 / (Real.sqrt x * x) := by
  have hsx_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsx_ne : Real.sqrt x ≠ 0 := ne_of_gt hsx_pos
  have hsum_pos : 0 < Real.sqrt x + Real.sqrt theta := by
    have hst_nonneg : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg theta
    linarith
  have hsum_sq_ge : x ≤ (Real.sqrt x + Real.sqrt theta) ^ 2 := by
    have hsx_sq : (Real.sqrt x) ^ 2 = x := by
      simpa using Real.sq_sqrt (le_of_lt hx)
    have hst_nonneg : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg theta
    nlinarith
  have hdisc : x - theta =
      (Real.sqrt x - Real.sqrt theta) *
        (Real.sqrt x + Real.sqrt theta) := by
    have hsx_sq : (Real.sqrt x) ^ 2 = x := by
      simpa using Real.sq_sqrt (le_of_lt hx)
    have hst_sq : (Real.sqrt theta) ^ 2 = theta := by
      simpa using Real.sq_sqrt htheta
    nlinarith
  rw [hdisc]
  have hden_pos : 0 < Real.sqrt x * x :=
    mul_pos hsx_pos hx
  apply (div_le_div_iff₀ hsx_pos hden_pos).2
  have hsq_nonneg : 0 ≤ (Real.sqrt x - Real.sqrt theta) ^ 2 :=
    sq_nonneg _
  calc
    (Real.sqrt x - Real.sqrt theta) ^ 2 * (Real.sqrt x * x)
        = ((Real.sqrt x - Real.sqrt theta) ^ 2 * x) * Real.sqrt x := by ring
    _ ≤ ((Real.sqrt x - Real.sqrt theta) ^ 2 *
          (Real.sqrt x + Real.sqrt theta) ^ 2) * Real.sqrt x := by
          gcongr
    _ = ((Real.sqrt x - Real.sqrt theta) *
          (Real.sqrt x + Real.sqrt theta)) ^ 2 * Real.sqrt x := by ring

#print axioms sqrt_gap_identity
#print axioms sqrt_gap_nonneg
#print axioms margin_sub_prefix_eq_tax
#print axioms prefix_le_margin
#print axioms prefix_pos_iff_integral_beats_tax
#print axioms prefix_pos_iff_critical_integral_gap
#print axioms sqrt_gap_tax_le_discrepancy_square

end RHPrimePrefixGapTax
