import Mathlib

/-!
# Rank-two reflection-pair determinant identity

Pure finite algebra used by the RH translation/exterior lane.
This file proves the polynomial identity behind the formula
`det(v w* + w v*) = - |det[v,w]|^2` for two complex 2-vectors,
without requiring any analytic input.

It does **not** prove RH.
-/

namespace RHProof
namespace TranslationPair

/--
Universal commutative-ring identity for a rank-two symmetrized outer-product
matrix.  In the complex specialization, take `ap,bp,cp,dp` to be the
complex conjugates of `a,b,c,d`; then the right-hand side is the negative
absolute square of the 2x2 exterior determinant.
-/
theorem symmetrized_outer_det
    {R : Type*} [CommRing R]
    (a b c d ap bp cp dp : R) :
    (a * cp + c * ap) * (b * dp + d * bp)
      - (a * dp + c * bp) * (b * cp + d * ap)
      = -(a * d - b * c) * (ap * dp - bp * cp) := by
  ring

/--
If the exterior determinant vanishes, then the determinant of the
symmetrized rank-two atom vanishes.  This is the finite algebraic direction
used for critical-line atoms after the two evaluation vectors become
collinear.
-/
theorem symmetrized_outer_det_zero_of_exterior_zero
    {R : Type*} [CommRing R]
    (a b c d ap bp cp dp : R)
    (h : a * d - b * c = 0) :
    (a * cp + c * ap) * (b * dp + d * bp)
      - (a * dp + c * bp) * (b * cp + d * ap) = 0 := by
  rw [symmetrized_outer_det]
  rw [h]
  ring

end TranslationPair
end RHProof
