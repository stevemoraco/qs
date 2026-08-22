import Mathlib

/-!
# BSD reciprocal-trace normalization firewall

This file formalizes only the elementary rational-function core of the
reciprocal-polynomial error isolated in Destrempes--Malinin Proposition 2.
It does not formalize division polynomials, elliptic curves, torsion fields,
Selmer groups, Sha, the source theorem, or BSD.
-/

namespace MillenniumBraid
namespace BSDReciprocalTraceFirewall

/-- For a quadratic monic polynomial `P(X)=(X-r)(X-s)`, the sum of the
reciprocals of the shifted roots is the negative logarithmic derivative
`-P'(e)/P(e)`.  The denominator is load-bearing. -/
theorem reciprocal_vieta_quadratic
    (r s e : ℚ) (hr : r ≠ e) (hs : s ≠ e) :
    1 / (r - e) + 1 / (s - e) =
      -(2 * e - r - s) / ((e - r) * (e - s)) := by
  field_simp [sub_ne_zero.mpr hr, sub_ne_zero.mpr hs,
    sub_ne_zero.mpr (Ne.symm hr), sub_ne_zero.mpr (Ne.symm hs)]
  ring

/-- Clearing the reciprocal variable in
`P(e+1/Y)` produces leading coefficient `P(e)`, not `1`. -/
theorem reciprocal_transform_quadratic
    (r s e Y : ℚ) (hY : Y ≠ 0) :
    Y ^ 2 * ((e + 1 / Y - r) * (e + 1 / Y - s)) =
      (e - r) * (e - s) * Y ^ 2 + (2 * e - r - s) * Y + 1 := by
  field_simp [hY]
  ring

/-- The smallest explicit counterexample to reading the reciprocal trace from
an unnormalized next-to-leading coefficient. -/
theorem reciprocal_quadratic_example :
    1 / (2 : ℚ) + 1 / 3 = 5 / 6 ∧
    1 / (2 : ℚ) + 1 / 3 ≠ 5 := by
  norm_num

/-- In the same example, the transformed polynomial has coefficients
`6 Y² - 5 Y + 1`; its leading coefficient is six. -/
theorem transformed_quadratic_example (Y : ℚ) (hY : Y ≠ 0) :
    Y ^ 2 * ((1 / Y - 2) * (1 / Y - 3)) =
      6 * Y ^ 2 - 5 * Y + 1 := by
  field_simp [hY]
  ring

/-- Dividing the next-to-leading coefficient by the leading coefficient gives
the correct reciprocal-root sum, while omitting the division gives the wrong
number. -/
theorem normalized_coefficient_example :
    -((-5 : ℚ) / 6) = 5 / 6 ∧ -(-5 : ℚ) = 5 ∧ (5 / 6 : ℚ) ≠ 5 := by
  norm_num

#print axioms reciprocal_vieta_quadratic
#print axioms reciprocal_transform_quadratic
#print axioms reciprocal_quadratic_example
#print axioms transformed_quadratic_example
#print axioms normalized_coefficient_example

end BSDReciprocalTraceFirewall
end MillenniumBraid
