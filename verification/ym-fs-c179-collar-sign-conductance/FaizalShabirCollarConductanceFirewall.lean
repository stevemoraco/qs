import Mathlib

/-!
# Faizal--Shabir collar sign and conductance firewalls

Finite algebra behind a hostile audit of arXiv:2606.19362v1, Eqs. (5.24)--(5.29).

The source prints the intended structural identity

`actual = ideal - discarded + error`

but later Eq. (5.26) prints

`ideal - actual = discarded + error`.

Those two sign conventions are incompatible for a nonzero error.  Preserving the
scale-correct structural identity forces

`ideal - actual = discarded - error`.

The source separately states that the collar error is self-adjoint and has
vanishing row and column sums.  In a symmetric Markov representation, the
positive part of the resulting quadratic-form debt can be paid by a relative
Dirichlet estimate if the harmful off-diagonal conductances are pointwise
controlled by the ideal transition conductances.  The finite summation theorem
below formalizes that consumer after the analytic kernel representation has been
supplied.

The final two declarations record a scale-critical countermodel: an absolute
error of order `t` tends to zero, but can overwhelm an ideal Dirichlet edge of
order `t^2`.  Thus zero-sum structure plus absolute `o(1)` smallness does not
supply the physical relative-form bound.

This file does not formalize Yang--Mills, the OS kernel representation, FRD,
polymer expansions, regulator/volume uniformity, continuum reconstruction, a
mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirCollarConductanceFirewall

/-- Preserving `actual = ideal - discarded + error` fixes the sign in the
corresponding difference identity. -/
theorem structural_identity_forces_difference_sign
    (ideal actual discarded error : ℝ)
    (h : actual = ideal - discarded + error) :
    ideal - actual = discarded - error := by
  linarith

/-- The plus-sign version of both displayed identities can coexist only when the
collar error vanishes. -/
theorem incompatible_plus_signs_force_zero_error
    (ideal actual discarded error : ℝ)
    (hstruct : actual = ideal - discarded + error)
    (hdiff : ideal - actual = discarded + error) :
    error = 0 := by
  linarith

/-- Pointwise domination of one harmful conductance contribution by an ideal
conductance contribution pays the corresponding squared-difference term. -/
theorem conductance_domination_term
    (bad good sq θ : ℝ)
    (hsq : 0 ≤ sq)
    (hdom : bad ≤ θ * good) :
    bad * sq ≤ θ * (good * sq) := by
  have h := mul_le_mul_of_nonneg_right hdom hsq
  simpa [mul_assoc] using h

/-- Finite-family form of the conductance-domination consumer.  In the QFT
application `sq i` is a squared difference, `bad i` is the harmful signed
collar conductance, and `good i` is the ideal Markov conductance. -/
theorem finite_conductance_domination
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (bad good sq : α → ℝ)
    (θ : ℝ)
    (hsq : ∀ i ∈ s, 0 ≤ sq i)
    (hdom : ∀ i ∈ s, bad i ≤ θ * good i) :
    (∑ i ∈ s, bad i * sq i) ≤
      θ * (∑ i ∈ s, good i * sq i) := by
  calc
    (∑ i ∈ s, bad i * sq i) ≤
        ∑ i ∈ s, θ * (good i * sq i) := by
      exact Finset.sum_le_sum fun i hi =>
        conductance_domination_term
          (bad i) (good i) (sq i) θ (hsq i hi) (hdom i hi)
    _ = θ * (∑ i ∈ s, good i * sq i) := by
      rw [Finset.mul_sum]

/-- An absolute tail of order `t` can dominate a physical edge of order `t^2`.
This is the scalar core of the warning that `error -> 0` is not a relative-form
estimate when the ideal transfer edge also closes. -/
theorem vanishing_absolute_tail_can_overwhelm_quadratic_edge
    (t θ : ℝ)
    (ht : 0 < t)
    (hrel : θ * t < 1) :
    θ * t ^ 2 < t := by
  have h := mul_lt_mul_of_pos_right hrel ht
  simpa [pow_two, mul_assoc] using h

/-- The same obstruction after multiplication by any strictly positive squared
difference weight. -/
theorem two_state_relative_energy_failure
    (t θ sq : ℝ)
    (ht : 0 < t)
    (hsq : 0 < sq)
    (hrel : θ * t < 1) :
    θ * (t ^ 2 * sq) < t * sq := by
  have h := vanishing_absolute_tail_can_overwhelm_quadratic_edge t θ ht hrel
  have h' := mul_lt_mul_of_pos_right h hsq
  simpa [mul_assoc] using h'

#print axioms structural_identity_forces_difference_sign
#print axioms incompatible_plus_signs_force_zero_error
#print axioms conductance_domination_term
#print axioms finite_conductance_domination
#print axioms vanishing_absolute_tail_can_overwhelm_quadratic_edge
#print axioms two_state_relative_energy_failure

end Millennium.YangMills.FaizalShabirCollarConductanceFirewall
