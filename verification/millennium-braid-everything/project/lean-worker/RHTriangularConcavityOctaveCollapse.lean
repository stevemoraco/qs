import Mathlib

namespace RHTriangularConcavityOctaveCollapse

/-!
# Finite algebra behind the triangular-concavity / octave-deficit collapse

The analytic prime-spline calculation identifies the following two scalar
expressions.  This file verifies their exact algebraic relation and the
corresponding sign equivalences.  It does not formalize the analytic derivation
of those expressions and does not prove RH.
-/

/-- Suzuki/octave deficit in abstract scalar coordinates. -/
def octaveDelta
    (gAtA gAtTwoA a expNegHalfA expNegA : ℝ) : ℝ :=
  gAtA - gAtTwoA - 2 * a + 4 * expNegHalfA - 4 * expNegA

/-- Second derivative of the scaled triangular discrepancy after the exact
prime-spline and continuous-main-term calculations. -/
def triangularSecond
    (gAtA gAtTwoA a expNegHalfA expNegA : ℝ) : ℝ :=
  4 * (gAtTwoA - gAtA) + 8 * a + 16 * expNegA - 16 * expNegHalfA

/-- Exact pointwise collapse: `F''(a) = -4 Δ(exp a)`. -/
theorem triangularSecond_eq_neg_four_octaveDelta
    (gAtA gAtTwoA a expNegHalfA expNegA : ℝ) :
    triangularSecond gAtA gAtTwoA a expNegHalfA expNegA =
      -4 * octaveDelta gAtA gAtTwoA a expNegHalfA expNegA := by
  simp [triangularSecond, octaveDelta]
  ring

/-- Strict concavity is exactly strict positivity of the octave deficit. -/
theorem triangularSecond_neg_iff_octaveDelta_pos
    (gAtA gAtTwoA a expNegHalfA expNegA : ℝ) :
    triangularSecond gAtA gAtTwoA a expNegHalfA expNegA < 0 ↔
      0 < octaveDelta gAtA gAtTwoA a expNegHalfA expNegA := by
  rw [triangularSecond_eq_neg_four_octaveDelta]
  constructor <;> intro h <;> linarith

/-- Nonpositive concavity is exactly nonnegative octave deficit. -/
theorem triangularSecond_nonpos_iff_octaveDelta_nonneg
    (gAtA gAtTwoA a expNegHalfA expNegA : ℝ) :
    triangularSecond gAtA gAtTwoA a expNegHalfA expNegA ≤ 0 ↔
      0 ≤ octaveDelta gAtA gAtTwoA a expNegHalfA expNegA := by
  rw [triangularSecond_eq_neg_four_octaveDelta]
  constructor <;> intro h <;> linarith

#print axioms triangularSecond_eq_neg_four_octaveDelta
#print axioms triangularSecond_neg_iff_octaveDelta_pos
#print axioms triangularSecond_nonpos_iff_octaveDelta_nonneg

end RHTriangularConcavityOctaveCollapse
