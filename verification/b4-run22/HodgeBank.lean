import Mathlib

/-!
# Hodge lane: Hilbert--Burch finite arithmetic firewall

For the audited Hilbert function
`h = (1, 2, 3, 4, 5, 6, 2, 1)`, this file checks the exact Hilbert
numerator
`(1 - T)^2 Σ h_i T^i = 1 - 5T^6 + 3T^7 + T^9`.
It also certifies the discriminant computation and excludes a rational
solution of
`3t^2 + 67t - 33138 = 0`.

This is only a finite polynomial-and-arithmetic certificate for one
Hilbert--Burch candidate. It does not formalize its geometric derivation,
the classification of Hilbert--Burch types, abelian varieties, or the
Hodge conjecture.
-/

namespace Millennium.Hodge.HilbertBurchArithmetic

open Polynomial

/-- The polynomial whose coefficients are the audited Hilbert function
`(1, 2, 3, 4, 5, 6, 2, 1)`. -/
noncomputable def hilbertFunctionPolynomial : Polynomial ℤ :=
  1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 +
    6 * X ^ 5 + 2 * X ^ 6 + X ^ 7

/-- Exact Hilbert numerator. As a polynomial identity, this records all
coefficients, including the zero coefficients not displayed on the right. -/
theorem hilbert_numerator :
    (1 - X) ^ 2 * hilbertFunctionPolynomial =
      1 - 5 * X ^ 6 + 3 * X ^ 7 + X ^ 9 := by
  unfold hilbertFunctionPolynomial
  ring

/-- The quadratic discriminant is `402145`; it lies strictly between
`634^2` and `635^2`, and is not a square even in `ℚ`.
The rational nonsquare check normalizes a rational square to coprime
numerator and denominator, so the consecutive-integer-square bracket is
not silently used as a real-number argument. -/
theorem discriminant_certificate :
    ((67 : ℤ) ^ 2 - 4 * 3 * (-33138) = 402145) ∧
      ((634 : ℕ) ^ 2 < 402145) ∧
      ((402145 : ℕ) < 635 ^ 2) ∧
      ¬ IsSquare (402145 : ℚ) := by
  norm_num

/-- The audited quadratic has no rational solution. Completing the square
would make its discriminant the rational square `(6t + 67)^2`, contrary
to `discriminant_certificate`. -/
theorem quadratic_has_no_rational_solution :
    ¬ ∃ t : ℚ, 3 * t ^ 2 + 67 * t - 33138 = 0 := by
  rintro ⟨t, ht⟩
  have hnot : ¬ IsSquare (402145 : ℚ) :=
    discriminant_certificate.2.2.2
  apply hnot
  refine ⟨6 * t + 67, ?_⟩
  nlinarith [ht]

#print axioms hilbert_numerator
#print axioms discriminant_certificate
#print axioms quadratic_has_no_rational_solution

end Millennium.Hodge.HilbertBurchArithmetic
