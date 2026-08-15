import Mathlib

/-!
# Fixed-UV source comparison

Finite scalar lemmas for the source-level Kirk-v4 fixed-UV coupling-window
reduction.

The point is deliberately narrow.  At a fixed positive weak-coupling window,
source rows of the form

  finite-size * u^2 + u^3 + bounded remainder

are uniformly `O(u^2)`.  Combined with a thermodynamic unit-tangent
`O(u^2)` coordinate, this yields the quadratic comparison required by
`FixedWeakCouplingWindow.lean`.

This file does not prove any Kirk source estimate, scheme identification,
beta-function theorem, Lambda theorem, Osterwalder--Schrader construction,
mass gap, or Clay result.
-/

namespace Millennium.YangMills

/-- If the scheduled finite-size modulus is at most the coupling, its
contribution `delta * u^2` is cubic. -/
theorem scheduled_modulus_row_is_cubic
    {u delta : ℝ}
    (hdelta : delta ≤ u) :
    delta * u ^ 2 ≤ u ^ 3 := by
  calc
    delta * u ^ 2 ≤ u * u ^ 2 :=
      mul_le_mul_of_nonneg_right hdelta (sq_nonneg u)
    _ = u ^ 3 := by ring

/-- On a fixed upper weak-coupling window, cubic errors are uniformly
quadratic. -/
theorem cubic_is_quadratic_on_upper_window
    {u uMax : ℝ}
    (huMax : u ≤ uMax) :
    u ^ 3 ≤ uMax * u ^ 2 := by
  calc
    u ^ 3 = u * u ^ 2 := by ring
    _ ≤ uMax * u ^ 2 :=
      mul_le_mul_of_nonneg_right huMax (sq_nonneg u)

/-- A uniformly bounded remainder on a positive lower coupling window can be
paid by a quadratic budget. -/
theorem bounded_remainder_absorbed_by_positive_window
    {u uMin r B Q : ℝ}
    (huMin : 0 < uMin)
    (hu : uMin ≤ u)
    (hQ : 0 ≤ Q)
    (hr : |r| ≤ B)
    (hBudget : B ≤ Q * uMin ^ 2) :
    |r| ≤ Q * u ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have hsq : uMin ^ 2 ≤ u ^ 2 := by
    nlinarith
  have hmono : Q * uMin ^ 2 ≤ Q * u ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hQ
  exact le_trans hr (le_trans hBudget hmono)

/-- Two quadratic coordinate-comparison rows compose with the sum of their
coefficients. -/
theorem quadratic_comparison_chain
    {u h hInf A B : ℝ}
    (hFinite : |h - hInf| ≤ A * u ^ 2)
    (hThermo : |hInf - u| ≤ B * u ^ 2) :
    |h - u| ≤ (A + B) * u ^ 2 := by
  rw [show h - u = (h - hInf) + (hInf - u) by ring]
  calc
    |(h - hInf) + (hInf - u)|
        ≤ |h - hInf| + |hInf - u| := abs_add_le _ _
    _ ≤ A * u ^ 2 + B * u ^ 2 := add_le_add hFinite hThermo
    _ = (A + B) * u ^ 2 := by ring

/-- Package the source-shaped finite-volume comparison into one uniform
quadratic error.  The remaining term `flat` is assumed already absorbed into
`Q * u^2`, which is automatic on a fixed positive compact coupling window
once it has a regulator-independent finite bound. -/
theorem source_comparison_gives_uniform_quadratic_error
    {u uMax delta flat h hInf C0 CInf Q : ℝ}
    (huMax : u ≤ uMax)
    (hdelta : delta ≤ u)
    (hQ : flat ≤ Q * u ^ 2)
    (hC0 : 0 ≤ C0)
    (hFinite :
      |h - hInf| ≤ C0 * (delta * u ^ 2 + u ^ 3 + flat))
    (hThermo : |hInf - u| ≤ CInf * u ^ 2) :
    |h - u| ≤ (C0 * (2 * uMax + Q) + CInf) * u ^ 2 := by
  have hdelta3 : delta * u ^ 2 ≤ u ^ 3 :=
    scheduled_modulus_row_is_cubic hdelta
  have h3 : u ^ 3 ≤ uMax * u ^ 2 :=
    cubic_is_quadratic_on_upper_window huMax
  have hinside :
      delta * u ^ 2 + u ^ 3 + flat ≤ (2 * uMax + Q) * u ^ 2 := by
    nlinarith
  have hFinite' :
      |h - hInf| ≤ (C0 * (2 * uMax + Q)) * u ^ 2 := by
    calc
      |h - hInf| ≤ C0 * (delta * u ^ 2 + u ^ 3 + flat) := hFinite
      _ ≤ C0 * ((2 * uMax + Q) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hinside hC0
      _ = (C0 * (2 * uMax + Q)) * u ^ 2 := by ring
  exact quadratic_comparison_chain hFinite' hThermo

#print axioms scheduled_modulus_row_is_cubic
#print axioms cubic_is_quadratic_on_upper_window
#print axioms bounded_remainder_absorbed_by_positive_window
#print axioms quadratic_comparison_chain
#print axioms source_comparison_gives_uniform_quadratic_error

end Millennium.YangMills
