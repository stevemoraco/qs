import Mathlib

/-!
# Hodge r=3 exceptional tangent-strata finite core

Exact algebraic identities from the current `r=3` double-plane/conductor
analysis.  These are finite polynomial certificates only.  They do not prove
coverage of the geometric strata, existence/nonexistence of the Severi curve,
or the Hodge conjecture.
-/

namespace Millennium.Hodge.R3ExceptionalTangentFinite

/-- Under the tangent-cone relation `4 b^3 = c d^2 - 27 a`, the banked
weight-12 term has the stated reduced form.  The relation is passed explicitly;
no geometric coverage assertion is hidden here. -/
theorem weight12_reduction
    (B a b c d : ℚ)
    (h : 4 * b^3 = c * d^2 - 27 * a) :
    -54 * B * a^2 - 36 * B * a * b^3 - 4 * B * b^6 =
      B * (27 * a^2 + 18 * a * c * d^2 - c^2 * d^4) / 4 := by
  have hb : b^3 = (c * d^2 - 27 * a) / 4 := by linarith
  rw [show b^6 = (b^3)^2 by ring, hb]
  ring

/-- The weight-12 residual factor cannot vanish merely by setting `a=0`
unless the remaining `c*d` factor also vanishes. -/
theorem weight12_at_a_zero (c d : ℚ) :
    27 * (0 : ℚ)^2 + 18 * 0 * c * d^2 - c^2 * d^4 = -c^2 * d^4 := by
  ring

/-- Exact polynomial form of the deepest repeated-root branch substitution
`b=g h`, `a=g^3 h^2(c g-4h)/27` in
`Phi_14 = -A^2 b (24a+b^3)`. -/
theorem weight14_deep_branch_factor
    (A c g h : ℚ) :
    -A^2 * (g*h) *
        (24 * (g^3 * h^2 * (c*g - 4*h) / 27) + (g*h)^3) =
      A^2 * g^4 * h^3 * (23*h - 8*c*g) / 9 := by
  ring

/-- After removing the exact `g^4` factor, the residual at `g=0` is the
coefficient `(23/9) A^2 h^4`.  Hence any geometric argument requiring order at
least seven must supply an additional reason forcing this coefficient to zero. -/
theorem weight14_leading_coefficient (A h : ℚ) :
    A^2 * h^3 * (23*h - 8 * (0 : ℚ)) / 9 =
      (23 : ℚ) / 9 * A^2 * h^4 := by
  ring

/-- Repeated-b endpoint identity: `b=l^2`, `d=l^3` forces the displayed
`tangent-cone` value of `a`. -/
theorem repeated_b_endpoint (c l : ℚ) :
    (c * (l^3)^2 - 4 * (l^2)^3) / 27 =
      (c - 4) * l^6 / 27 := by
  ring

/-- Rationalized Fermat-cubic identity.  Introducing a formal `s` with
`27 s^2 = (u^3-v^3)^2` avoids adjoining `sqrt 3`; this is exactly the square
identity used by the symbolic checker. -/
theorem fermat_cubic_tangent_identity
    (u v s : ℚ)
    (hs : 27 * s^2 = (u^3 - v^3)^2) :
    (u^3 + v^3)^2 - 27*s^2 - 4*(u*v)^3 = 0 := by
  rw [hs]
  ring

#print axioms weight12_reduction
#print axioms weight12_at_a_zero
#print axioms weight14_deep_branch_factor
#print axioms weight14_leading_coefficient
#print axioms repeated_b_endpoint
#print axioms fermat_cubic_tangent_identity

end Millennium.Hodge.R3ExceptionalTangentFinite
