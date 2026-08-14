import Mathlib

/-!
# Yu fixed-filter L2 work-compactness finite core

Finite real-algebra shadows of the functional-analytic reduction in
`stevemoraco/RH`: at one fixed filter scale, strong local L2 convergence plus a
uniform energy bound controls the quadratic stress difference, while convergence
of the resolved test controls the bilinear work pairing.

This file does NOT formalize convolution, Aubin--Lions, suitable weak solutions,
Yu's commutator theorem, pressure/localization estimates, Navier--Stokes
regularity, or blow-up.
-/

namespace NSYuL2WorkCompactness

/-- Difference of quadratic products factors through the input difference. -/
theorem quadratic_product_difference_identity (a b : ℝ) :
    a * a - b * b = (a - b) * a + b * (a - b) := by
  ring

/-- Scalar shadow of
`||u_n tensor u_n - u tensor u||_1 <= (||u_n||_2+||u||_2)||u_n-u||_2`. -/
theorem quadratic_product_difference_bound (a b : ℝ) :
    |a * a - b * b| ≤ (|a| + |b|) * |a - b| := by
  rw [quadratic_product_difference_identity]
  calc
    |(a - b) * a + b * (a - b)|
        ≤ |(a - b) * a| + |b * (a - b)| := abs_add_le _ _
    _ = (|a| + |b|) * |a - b| := by
      rw [abs_mul, abs_mul]
      ring

/-- Exact decomposition of a stress/test work difference. -/
theorem bilinear_work_difference_identity (rn r tn t : ℝ) :
    rn * tn - r * t = (rn - r) * tn + r * (tn - t) := by
  ring

/-- Scalar shadow of the fixed-filter work-pairing continuity estimate. -/
theorem bilinear_work_difference_bound (rn r tn t : ℝ) :
    |rn * tn - r * t| ≤
      |rn - r| * |tn| + |r| * |tn - t| := by
  rw [bilinear_work_difference_identity]
  calc
    |(rn - r) * tn + r * (tn - t)|
        ≤ |(rn - r) * tn| + |r * (tn - t)| := abs_add_le _ _
    _ = |rn - r| * |tn| + |r| * |tn - t| := by
      rw [abs_mul, abs_mul]

/-- If stress error and test error are both linear in one compactness error,
then the work error is linear in the same error. This is the finite algebra
behind freezing a filter ratio first and applying ordinary local compactness. -/
theorem work_error_linear_budget
    (A B C D du rErr tBound rBound tErr workErr : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdu : 0 ≤ du)
    (htBound : 0 ≤ tBound) (htErr : 0 ≤ tErr)
    (hr : rErr ≤ A * du)
    (htb : tBound ≤ B)
    (hrb : rBound ≤ C)
    (hte : tErr ≤ D * du)
    (hw : workErr ≤ rErr * tBound + rBound * tErr) :
    workErr ≤ (A * B + C * D) * du := by
  have hAdu : 0 ≤ A * du := mul_nonneg hA hdu
  have h1 : rErr * tBound ≤ (A * du) * B :=
    mul_le_mul hr htb htBound hAdu
  have h2 : rBound * tErr ≤ C * (D * du) :=
    mul_le_mul hrb hte htErr hC
  calc
    workErr ≤ rErr * tBound + rBound * tErr := hw
    _ ≤ (A * du) * B + C * (D * du) := add_le_add h1 h2
    _ = (A * B + C * D) * du := by ring

/-- A vanishing stress error alone is not enough if the test amplitude is allowed
to diverge at the reciprocal rate. This prevents silently dropping the
fixed-filter bounded-test hypothesis when passing work to a limit. -/
theorem vanishing_stress_error_with_diverging_test_can_keep_unit_work
    {n : ℝ} (hn : n ≠ 0) :
    (1 / n) * n = 1 := by
  field_simp [hn]

#print axioms quadratic_product_difference_identity
#print axioms quadratic_product_difference_bound
#print axioms bilinear_work_difference_identity
#print axioms bilinear_work_difference_bound
#print axioms work_error_linear_budget
#print axioms vanishing_stress_error_with_diverging_test_can_keep_unit_work

end NSYuL2WorkCompactness
