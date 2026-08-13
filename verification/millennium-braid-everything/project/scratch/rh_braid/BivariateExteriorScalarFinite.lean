import Mathlib

/-!
# Finite scalar algebra for the bivariate exterior RH correlator

This file formalizes only the polynomial identity

  P(M,N) = tr(M) tr(N) - tr(MN) = a*h + d*e - 2*b*f

for symmetric 2x2 matrices, together with the derivative substitution used in the
first-jet scalar reduction.  It does not prove RH.
-/

namespace RHProof
namespace BivariateExteriorScalar

/-- Polarized 2x2 determinant identity for symmetric matrices. -/
theorem polarized_two_by_two
    (a b d e f h : ℂ) :
    (a + d) * (e + h) - (a * e + b * f + b * f + d * h)
      = a * h + d * e - 2 * b * f := by
  ring

/-- First-jet derivative substitution:
`b = i Ft'`, `f = i Fs'`, `d = -Ft''`, `h = -Fs''`.
The exterior polarization becomes the scalar Wronskian/Hankel expression. -/
theorem first_jet_scalar_reduction
    (Ft Fpt Fppt Fs Fps Fpps : ℂ) :
    Ft * (-Fpps) + (-Fppt) * Fs
        - 2 * (Complex.I * Fpt) * (Complex.I * Fps)
      = 2 * Fpt * Fps - Ft * Fpps - Fppt * Fs := by
  rw [Complex.I_mul_I]
  ring

/-- Diagonal specialization. -/
theorem diagonal_first_jet
    (F Fp Fpp : ℂ) :
    2 * Fp * Fp - F * Fpp - Fpp * F
      = 2 * (Fp^2 - F * Fpp) := by
  ring

end BivariateExteriorScalar
end RHProof
