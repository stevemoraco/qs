import Mathlib

/-!
Finite algebraic core of the ring-mode helical-feedback cancellation.

This file does NOT formalize Navier–Stokes, Euler, cylindrical divergence,
or the Albritton–Ożański asymptotics. It formalizes only the load-bearing
scalar identity obtained after those analytic quantities have been defined.
-/

namespace NSRingHelicalFeedbackCancellation

/-- If the tangential Reynolds component is decomposed as
    `Rrtheta = beta * r * S + E`, then the helical combination of the
    axisymmetric mean-feedback components cancels the derivative of `S`.

    Here `Sp` and `Ep` stand for radial derivatives of `S` and `E` at a
    fixed radius. -/
theorem helical_feedback_cancellation
    (beta r S E Sp Ep : ℝ) (hr : r ≠ 0) :
    (-beta * (Sp + S / r))
      + ((beta * (S + r * Sp) + Ep) / r
          + 2 * (beta * r * S + E) / (r^2))
      = 2 * beta * S / r + Ep / r + 2 * E / (r^2) := by
  field_simp [hr]
  ring

/-- The sign consequence used in the mean-feedback anti-alignment note:
    a strictly positive growth rate and a strictly positive mode energy
    force a strictly negative parent/feedback pairing. -/
theorem anti_alignment
    (lambda energy pairing : ℝ)
    (hlambda : 0 < lambda)
    (henergy : 0 < energy)
    (hpair : pairing = -(lambda * energy)) :
    pairing < 0 := by
  rw [hpair]
  positivity

#print axioms helical_feedback_cancellation
#print axioms anti_alignment

end NSRingHelicalFeedbackCancellation
