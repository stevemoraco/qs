import Mathlib

set_option linter.unnecessarySeqFocus false

/-!
# Cubic RG recurrence subleading-normalization firewall

This file isolates a finite algebraic obstruction behind a load-bearing
Yang--Mills dimensional-transmutation normalization step.

Consider a scalar weak-coupling recurrence

    u' = u + b u^2 + c u^3.

The leading quadratic coefficient `b` fixes the leading reciprocal clock
`1 / (b u)`.  But the cubic coefficient already changes the first correction
to one-step progress of that clock.  Therefore agreement only through the
quadratic (one-loop-style) term does not, by finite algebra alone, determine
the subleading logarithmic normalization of a first-crossing scale.

The exact identities below are only a finite scalar firewall.  They do not
formalize an actual Yang--Mills beta function, prove a hitting-time asymptotic,
identify the universal two-loop coefficient, compare renormalization schemes,
construct an Osterwalder--Schrader limit, or prove a mass gap.
-/

namespace Millennium.YangMills

/-- Cubic model for one weak-coupling RG step. -/
def cubicRGStep (b c u : ℝ) : ℝ :=
  u + b * u ^ 2 + c * u ^ 3

/-- Progress of the leading reciprocal clock `1 / (b u)` in one RG step. -/
noncomputable def reciprocalClockProgress (b c u : ℝ) : ℝ :=
  1 / (b * u) - 1 / (b * cubicRGStep b c u)

/-- Exact one-step reciprocal-clock progress for the cubic recurrence. -/
theorem reciprocalClockProgress_exact
    {b c u : ℝ}
    (hb : b ≠ 0)
    (hu : u ≠ 0)
    (hden : 1 + b * u + c * u ^ 2 ≠ 0) :
    reciprocalClockProgress b c u =
      (1 + (c / b) * u) / (1 + b * u + c * u ^ 2) := by
  have hfactor : cubicRGStep b c u = u * (1 + b * u + c * u ^ 2) := by
    simp [cubicRGStep]
    ring
  rw [reciprocalClockProgress, hfactor]
  field_simp [hb, hu, hden] <;> ring

/-- The defect from one unit of reciprocal-clock progress depends explicitly
on the cubic coefficient `c`. -/
theorem reciprocalClockProgress_sub_one_exact
    {b c u : ℝ}
    (hb : b ≠ 0)
    (hu : u ≠ 0)
    (hden : 1 + b * u + c * u ^ 2 ≠ 0) :
    reciprocalClockProgress b c u - 1 =
      (((c / b - b) * u - c * u ^ 2) /
        (1 + b * u + c * u ^ 2)) := by
  rw [reciprocalClockProgress_exact hb hu hden]
  field_simp [hden] <;> ring

/-- Two recurrences with the same linear and quadratic terms can differ only
at cubic order.  Here `c = 0` and `c = 1` differ by exactly `u^3`. -/
theorem same_quadratic_data_cubic_difference (u : ℝ) :
    cubicRGStep 1 1 u - cubicRGStep 1 0 u = u ^ 3 := by
  simp [cubicRGStep]

/-- For the recurrence `u' = u + u^2`, the normalized reciprocal-clock defect
is exactly `-1/(1+u)`. -/
theorem quadratic_step_normalized_clock_defect
    {u : ℝ}
    (hu : u ≠ 0)
    (hden : 1 + u ≠ 0) :
    (reciprocalClockProgress 1 0 u - 1) / u = -1 / (1 + u) := by
  have hbase := reciprocalClockProgress_sub_one_exact
    (b := (1 : ℝ)) (c := (0 : ℝ)) (u := u)
    (by norm_num) hu (by simpa using hden)
  rw [hbase]
  field_simp [hu, hden] <;> ring

/-- Adding the cubic term `u^3`, while leaving the same quadratic data, changes
the normalized reciprocal-clock defect to `-u/(1+u+u^2)`. -/
theorem cubic_step_normalized_clock_defect
    {u : ℝ}
    (hu : u ≠ 0)
    (hden : 1 + u + u ^ 2 ≠ 0) :
    (reciprocalClockProgress 1 1 u - 1) / u =
      -u / (1 + u + u ^ 2) := by
  have hbase := reciprocalClockProgress_sub_one_exact
    (b := (1 : ℝ)) (c := (1 : ℝ)) (u := u)
    (by norm_num) hu (by simpa using hden)
  rw [hbase]
  field_simp [hu, hden] <;> ring

#print axioms reciprocalClockProgress_exact
#print axioms reciprocalClockProgress_sub_one_exact
#print axioms same_quadratic_data_cubic_difference
#print axioms quadratic_step_normalized_clock_defect
#print axioms cubic_step_normalized_clock_defect

end Millennium.YangMills
