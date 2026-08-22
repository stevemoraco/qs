import Mathlib

namespace NSTrilinearResponseParityFinite

/-!
Abstract algebraic core of the torus-involution response theorem.

`b` is an abstract trilinear-response evaluator and `S` an abstract symmetry.
The human theorem separately proves the concrete Navier--Stokes torus action is
unitary and preserves the actual trilinear form and Leray projection.

This file formalizes only the consequence of invariance once those analytic
premises have been supplied.
-/

variable {V : Type*}

/-- Symmetrized response of an ordered pair against a test profile. -/
def response (b : V → V → V → ℝ) (phi u v : V) : ℝ :=
  b u v phi + b v u phi

/-- A symmetry-even test profile gives a symmetry-even pair response. -/
theorem even_response_transport
    (b : V → V → V → ℝ) (S : V → V)
    (phi u v : V)
    (hinv : ∀ a d w, b (S a) (S d) (S w) = b a d w)
    (heven : S phi = phi) :
    response b phi (S u) (S v) = response b phi u v := by
  unfold response
  have h1 := hinv u v phi
  have h2 := hinv v u phi
  rw [heven] at h1 h2
  rw [h1, h2]

/-- A symmetry-odd test profile gives a symmetry-odd pair response, assuming
linearity under negation in the tested coordinate. -/
theorem odd_response_transport
    [Neg V]
    (b : V → V → V → ℝ) (S : V → V)
    (phi u v : V)
    (hinv : ∀ a d w, b (S a) (S d) (S w) = b a d w)
    (hneg : ∀ a d w, b a d (-w) = -b a d w)
    (hodd : S phi = -phi) :
    response b phi (S u) (S v) = -response b phi u v := by
  unfold response
  have h1 := hinv u v phi
  have h2 := hinv v u phi
  rw [hodd, hneg] at h1 h2
  linarith

/-- One even and one odd test profile turn one pair and its symmetry image into
response columns `(p,c)` and `(p,-c)`. -/
theorem opposite_character_columns
    [Neg V]
    (b : V → V → V → ℝ) (S : V → V)
    (phiEven phiOdd u v : V)
    (hinv : ∀ a d w, b (S a) (S d) (S w) = b a d w)
    (hneg : ∀ a d w, b a d (-w) = -b a d w)
    (heven : S phiEven = phiEven)
    (hodd : S phiOdd = -phiOdd) :
    response b phiEven (S u) (S v) = response b phiEven u v ∧
      response b phiOdd (S u) (S v) = -response b phiOdd u v := by
  constructor
  · exact even_response_transport b S phiEven u v hinv heven
  · exact odd_response_transport b S phiOdd u v hinv hneg hodd

/-- If the even seed response is positive and the requested target is
nonnegative, the equal-weight symmetry-orbit repair coefficient is
nonnegative. -/
theorem orbit_equal_weight_nonnegative
    {target evenResponse : ℝ}
    (htarget : 0 ≤ target)
    (heven : 0 < evenResponse) :
    0 ≤ target / (2 * evenResponse) := by
  exact div_nonneg htarget (mul_nonneg (by norm_num) (le_of_lt heven))

#print axioms even_response_transport
#print axioms odd_response_transport
#print axioms opposite_character_columns
#print axioms orbit_equal_weight_nonnegative

end NSTrilinearResponseParityFinite
