import Mathlib

/-!
Finite polynomial shadow of `stevemoraco/RH#381`.

Formalized here only:
* the denominator-free splitting-preserving completion-of-the-square identity;
* the canonical reduced-NG21 binary-cubic discriminant `4 * ell^5 * m`;
* the algebraic factorization used at the single-root Faenzi--Stipins chart;
* the exact determinant of the quadratic tangent Hessian at the double-root
  endpoint and the scalar fact that a nonzero `tau*z` coefficient forces that
  determinant to be nonzero when the `u^2` coefficient is nonzero;
* the rank-one two-variable minor ledger.

Not formalized here:
Tschirnhausen bundles or their automorphism groups, the permission to make the
splitting-preserving shear globally on `P1`, Miranda/Delone--Faddeev geometry,
Faenzi--Stipins' birational model, analytic coordinate changes, rational/ADE or
minimally elliptic singularity theory, the banked exceptional graph, K3
geometry, or the Hodge conjecture.  In particular, no axiom below carries any
Hodge conclusion.
-/

namespace Millennium.Hodge.R3Q1A7NG21CanonicalMirandaFiniteCore

/-- Binary-cubic discriminant in coefficient order `(a,b,c,d)`. -/
def cubicDisc (a b c d : ℚ) : ℚ :=
  b^2 * c^2 - 4*a*c^3 - 4*b^3*d - 27*a^2*d^2 + 18*a*b*c*d

/-- Denominator-free form of the NG21 completion of the square.  The human
geometric bridge is `hquad`, the degree-two normalized branch discriminant. -/
theorem splitting_preserving_completion_square
    (ell m beta kappa c1 d2 Z W : ℚ)
    (hquad : c1^2 - 4 * beta * d2 = kappa * ell * m) :
    4 * beta * (beta * Z^2 + c1 * Z * W + d2 * W^2)
      = (2 * beta * Z + c1 * W)^2 - kappa * ell * m * W^2 := by
  rw [← hquad]
  ring

/-- The canonical vertical cubic `ell*W*(Z^2-ell*m*W^2)` has the exact
`5+1` discriminant, up to the harmless nonzero scalar `4`. -/
theorem canonical_vertical_discriminant (ell m : ℚ) :
    cubicDisc 0 ell 0 (-ell^2 * m) = 4 * ell^5 * m := by
  simp [cubicDisc]
  ring

/-- Pure algebra behind the single-root chart: all higher powers of `w` factor
through the coefficient of the local coordinate which has nonzero `u`
derivative in the human argument. -/
theorem single_root_chart_factorization
    (A0 A1 A2 A3 w : ℚ) :
    A0 + A1*w + A2*w^2 + A3*w^3
      = A0 + w * (A1 + A2*w + A3*w^2) := by
  ring

/-- Determinant of the Hessian of
`A*tau^2 + B*tau*u + C*u^2 + D*tau*z` in `(tau,u,z)`. -/
def tangentHessianDet (A B C D : ℚ) : ℚ :=
    (2*A) * ((2*C)*0 - 0*0)
      - B * (B*0 - 0*D)
      + D * (B*0 - (2*C)*D)

/-- Exact 3x3 Hessian determinant ledger. -/
theorem tangent_hessian_det_formula (A B C D : ℚ) :
    tangentHessianDet A B C D = -2 * C * D^2 := by
  simp [tangentHessianDet]
  ring

/-- If the `u^2` coefficient and the `tau*z` coefficient are both nonzero, the
quadratic tangent Hessian is nondegenerate.  The geometric use is the
contrapositive: a non-rational endpoint cannot retain such a cross term. -/
theorem cross_term_forces_nonzero_hessian
    (A B C D : ℚ) (hC : C ≠ 0) (hD : D ≠ 0) :
    tangentHessianDet A B C D ≠ 0 := by
  rw [tangent_hessian_det_formula]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hC) (pow_ne_zero 2 hD)

/-- Determinant of the remaining `(tau,u)` quadratic block after the `tau*z`
coefficient is killed. -/
def tangentTwoByTwoMinor (A B C : ℚ) : ℚ :=
    (2*A) * (2*C) - B^2

/-- Rank-one scalar ledger for the remaining quadratic block. -/
theorem tangent_two_by_two_minor_formula (A B C : ℚ) :
    tangentTwoByTwoMinor A B C = 4*A*C - B^2 := by
  simp [tangentTwoByTwoMinor]
  ring

#check splitting_preserving_completion_square
#check canonical_vertical_discriminant
#check single_root_chart_factorization
#check tangent_hessian_det_formula
#check cross_term_forces_nonzero_hessian
#check tangent_two_by_two_minor_formula

#print axioms splitting_preserving_completion_square
#print axioms canonical_vertical_discriminant
#print axioms single_root_chart_factorization
#print axioms tangent_hessian_det_formula
#print axioms cross_term_forces_nonzero_hessian
#print axioms tangent_two_by_two_minor_formula

end Millennium.Hodge.R3Q1A7NG21CanonicalMirandaFiniteCore
