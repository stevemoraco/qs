import Mathlib

/-!
Finite polynomial companion to `stevemoraco/RH#314`.

This file verifies only the explicit cubic discriminant identity and the two
integer degree ledgers used by the human normalization/conductor argument.  It
does not formalize F4, K3 surfaces, normalization, trace discriminants,
conductors, Riemann--Hurwitz, Severi loci, or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3DiscriminantConductorFinite

variable {R : Type*} [CommRing R]

def cubicDisc (c3 c2 c1 c0 : R) : R :=
  c2 ^ 2 * c1 ^ 2
    - 4 * c3 * c1 ^ 3
    - 4 * c2 ^ 3 * c0
    - 27 * c3 ^ 2 * c0 ^ 2
    + 18 * c3 * c2 * c1 * c0

def residualPhi (A B a b alpha : R) : R :=
  4 * A ^ 3 * alpha ^ 6
    - 24 * A ^ 2 * a * b * alpha ^ 4
    - A ^ 2 * b ^ 4 * alpha ^ 2
    + 18 * A * B * b ^ 2 * alpha ^ 4
    + 30 * A * a ^ 2 * b ^ 2 * alpha ^ 2
    + 4 * A * a * b ^ 5
    + 27 * B ^ 2 * alpha ^ 6
    - 54 * B * a ^ 2 * alpha ^ 4
    - 36 * B * a * b ^ 3 * alpha ^ 2
    - 4 * B * b ^ 6
    + 27 * a ^ 4 * alpha ^ 2
    + 4 * a ^ 3 * b ^ 3

/-- Exact denominator-free discriminant factorization for
`alpha^2*(x^3+A*x+B) - (a+b*x)^2`. -/
theorem cubic_discriminant_factor
    (A B a b alpha : R) :
    cubicDisc
        (alpha ^ 2)
        (-(b ^ 2))
        (alpha ^ 2 * A - 2 * a * b)
        (alpha ^ 2 * B - a ^ 2)
      = -(alpha ^ 2) * residualPhi A B a b alpha := by
  simp only [cubicDisc, residualPhi]
  ring

/-- For a genus-one normalization of an arithmetic-genus-ten cubic cover,
the degree-24 discriminant ledger splits as twice conductor degree nine plus
normalized degree-three branch degree six. -/
theorem conductor_degree_ledger :
    (24 : ℤ) = 2 * 9 + 6 := by
  norm_num

/-- The residual discriminant is sextic in the projective square-form
parameters, so a projective degree-13 parameter curve pulls its coefficients
back in degree 78. -/
theorem parameter_degree_ledger :
    (78 : ℤ) = 6 * 13 := by
  norm_num

#print axioms cubic_discriminant_factor
#print axioms conductor_degree_ledger
#print axioms parameter_degree_ledger

end Millennium.Hodge.R3DiscriminantConductorFinite
