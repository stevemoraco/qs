import Mathlib

/-!
Finite polynomial shadow of `stevemoraco/RH#389`, stacked on the canonical
Miranda finite core from `RH-Lean#1206`.

Formalized here only:
* the exact denominator-free vertical critical-value identity
    `4 (u z^2-u^2)=z^4-(2u-z^2)^2`;
* the elementary factorization of the parent cubic discriminant gate;
* the coefficient characterization of a pure triple-line cubic in the forced
  `t`-divisible family;
* the trivial zero-cubic coefficient ledger.

Not formalized here:
analytic Morse/splitting lemmas, Hensel or Weierstrass preparation, isolated
plane-curve factorization, the reduction of a double-plus-simple cubic to a
`D_n` rational double point, Kas' minimal-Weierstrass theorem, the
semiquasihomogeneous `E_6` classification, Faenzi--Stipins/Miranda geometry,
minimal elliptic singularities, K3 surfaces, algebraic cycles, or the Hodge
conjecture.  No axiom below carries any such conclusion.
-/

namespace Millennium.Hodge.R3Q1A7NG21CubicVanishingFiniteCore

/-- Exact polynomial completion of the square on the canonical NG21 vertical
slice.  The human geometric use is that the critical value at `2*u=z^2` has a
nonzero quartic `z^4` term. -/
theorem vertical_critical_value_identity (u z : ℚ) :
    4 * (u * z^2 - u^2) = z^4 - (2*u - z^2)^2 := by
  ring

/-- The parent discriminant equation has exactly the two elementary algebraic
factors used by the human case split. -/
theorem cubic_discriminant_zero_cases
    (A B C : ℚ) (h : C^2 * (B^2 - 4*A*C) = 0) :
    C = 0 ∨ B^2 = 4*A*C := by
  rcases mul_eq_zero.mp h with hC | hQ
  · left
    nlinarith
  · right
    nlinarith

/-- For the forced family `t*(A*t^2+B*t*z+C*t*z^2)`, being identically the pure
triple line `A*t^3` is equivalent to vanishing of the two mixed coefficients.
This is only coefficient algebra; the human theorem that every other
nonzero discriminant-zero cubic is double-plus-simple is not encoded. -/
theorem pure_triple_line_iff (A B C : ℚ) :
    (∀ t z : ℚ,
      A*t^3 + B*t^2*z + C*t*z^2 = A*t^3) ↔
      B = 0 ∧ C = 0 := by
  constructor
  · intro h
    have h1 := h 1 1
    have h2 := h 1 (-1)
    norm_num at h1 h2
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩ t z
    ring

/-- If all three coefficients vanish then the forced cubic tangent cone is
identically zero. -/
theorem zero_cubic_of_coefficients (A B C : ℚ)
    (hA : A = 0) (hB : B = 0) (hC : C = 0) :
    ∀ t z : ℚ, A*t^3 + B*t^2*z + C*t*z^2 = 0 := by
  subst A
  subst B
  subst C
  intro t z
  ring

/-- Conversely, vanishing of the forced cubic polynomial as a function over
`ℚ` forces all three coefficients to vanish. -/
theorem coefficients_zero_of_zero_cubic
    (A B C : ℚ)
    (h : ∀ t z : ℚ, A*t^3 + B*t^2*z + C*t*z^2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have hA := h 1 0
  have hP := h 1 1
  have hM := h 1 (-1)
  norm_num at hA hP hM
  constructor
  · exact hA
  · constructor <;> linarith

#check vertical_critical_value_identity
#check cubic_discriminant_zero_cases
#check pure_triple_line_iff
#check zero_cubic_of_coefficients
#check coefficients_zero_of_zero_cubic

#print axioms vertical_critical_value_identity
#print axioms cubic_discriminant_zero_cases
#print axioms pure_triple_line_iff
#print axioms zero_cubic_of_coefficients
#print axioms coefficients_zero_of_zero_cubic

end Millennium.Hodge.R3Q1A7NG21CubicVanishingFiniteCore
