import Mathlib

/-!
# Abe v26 tangent-intercept countermodel

This file formalizes the exact rational witness to a finite algebraic error in
equation (5.5) of Yukitaka Abe, *A rigorous proof of the Riemann hypothesis*,
Version 26, DOI `10.33774/coe-2022-d3nj5-v26`.

For `alpha = 2`, `beta = 1`, and `(R,I) = (2/5,1/5)`, all preceding circle
equations hold.  The tangent line used in the paper has true x-intercept
`2/3`, while the expression printed in (5.5), which omits the factor `I`, is
`26/15`.

Only this finite rational counterexample is formalized.  Nothing here proves
or disproves the Riemann hypothesis, formalizes the analytic xi-function
argument, or validates any other part of the manuscript.
-/

namespace RHAbeV26TangentIntercept

def alpha : ℚ := 2
def beta : ℚ := 1
def realCoordinate : ℚ := 2 / 5
def imaginaryCoordinate : ℚ := 1 / 5

def radicand : ℚ :=
  realCoordinate / alpha - realCoordinate ^ 2

/-- The relevant square root is rational for the selected witness. -/
def sqrtRadicand : ℚ := 1 / 5

/-- Slope of the tangent to the paper's second circle at the witness point. -/
def tangentSlope : ℚ :=
  (1 / (2 * alpha) - realCoordinate) / sqrtRadicand

/-- The actual x-intercept obtained by setting `Y = 0` in
`Y = tangentSlope * (X - R) + I`. -/
def trueIntercept : ℚ :=
  realCoordinate - imaginaryCoordinate / tangentSlope

/-- The expression printed in equation (5.5), lacking the factor `I`. -/
def paperIntercept : ℚ :=
  realCoordinate -
    sqrtRadicand / (1 / (2 * alpha) - realCoordinate)

/-- The witness satisfies the two scalar equations from which the manuscript's
two circles are derived. -/
theorem zeroEquationsHold :
    realCoordinate =
        alpha * (realCoordinate ^ 2 + imaginaryCoordinate ^ 2) ∧
      imaginaryCoordinate =
        beta * (realCoordinate ^ 2 + imaginaryCoordinate ^ 2) := by
  norm_num [alpha, beta, realCoordinate, imaginaryCoordinate]

/-- The witness lies on both circles displayed in Section 5. -/
theorem circleEquationsHold :
    realCoordinate ^ 2 +
          (imaginaryCoordinate - 1 / (2 * beta)) ^ 2 =
        1 / (4 * beta ^ 2) ∧
      (realCoordinate - 1 / (2 * alpha)) ^ 2 +
          imaginaryCoordinate ^ 2 =
        1 / (4 * alpha ^ 2) := by
  norm_num [alpha, beta, realCoordinate, imaginaryCoordinate]

/-- Exact positive square-root certificate used by the tangent formula. -/
theorem sqrtRadicandCertificate :
    0 < sqrtRadicand ∧ sqrtRadicand ^ 2 = radicand := by
  norm_num [sqrtRadicand, radicand, realCoordinate, alpha]

/-- The tangent slope at the witness is exactly `-3/4`. -/
theorem tangentSlopeValue : tangentSlope = -3 / 4 := by
  norm_num [tangentSlope, alpha, realCoordinate, sqrtRadicand]

/-- Solving the tangent equation gives the true x-intercept `2/3`. -/
theorem trueInterceptValue : trueIntercept = 2 / 3 := by
  norm_num [trueIntercept, tangentSlope, alpha, realCoordinate,
    imaginaryCoordinate, sqrtRadicand]

/-- Equation (5.5) gives `26/15` on the same exact witness. -/
theorem paperInterceptValue : paperIntercept = 26 / 15 := by
  norm_num [paperIntercept, alpha, realCoordinate, sqrtRadicand]

/-- The printed equation (5.5) is therefore not the tangent's x-intercept. -/
theorem equationFiveFiveFails : trueIntercept ≠ paperIntercept := by
  rw [trueInterceptValue, paperInterceptValue]
  norm_num

#print axioms zeroEquationsHold
#print axioms circleEquationsHold
#print axioms sqrtRadicandCertificate
#print axioms tangentSlopeValue
#print axioms trueInterceptValue
#print axioms paperInterceptValue
#print axioms equationFiveFiveFails

end RHAbeV26TangentIntercept
