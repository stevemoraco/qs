import Mathlib

/-!
# Faizal–Shabir Appendix A.10 firewall

Finite scalar audit of the deterministic recurrence used in Appendix A.9--A.10
of the Faizal–Shabir manuscript.

The printed induction asks, for positive `C,r`, that

`2 * C * r + C * r^2 <= 0`.

That condition is impossible.  The correct local mechanism is instead the
standard invariant-ball estimate: if `0 <= x <= r` and
`rho + C*r <= q`, then

`rho*x + C*x^2 <= q*x`.

In particular, `rho + C*r <= 1` makes the radius-`r` ball forward invariant;
a strict `q<1` gives a one-step contraction while the trajectory remains in
the ball.

This file does not formalize the Yang–Mills RG map, the Gaussian/center
projection used in Appendix A.9, regulator/volume uniformity, AF/IR
identification, continuum OS reconstruction, or a mass gap.
-/

namespace Millennium.YangMills.FaizalShabirAppendixA10Firewall

theorem printed_closing_condition_impossible
    (C r : ℝ)
    (hC : 0 < C)
    (hr : 0 < r) :
    ¬ (2 * C * r + C * r ^ 2 <= 0) := by
  intro h
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have h1 : 0 < 2 * C * r := by positivity
  have h2 : 0 < C * r ^ 2 := mul_pos hC hr2
  linarith

theorem one_step_contraction_inside_ball
    (rho C r q x : ℝ)
    (hC : 0 <= C)
    (hx0 : 0 <= x)
    (hxr : x <= r)
    (hmargin : rho + C * r <= q) :
    rho * x + C * x ^ 2 <= q * x := by
  have hxx : x * x <= r * x :=
    mul_le_mul_of_nonneg_right hxr hx0
  have hquad : C * x ^ 2 <= C * r * x := by
    simpa [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hxx hC
  have hlin : (rho + C * r) * x <= q * x :=
    mul_le_mul_of_nonneg_right hmargin hx0
  calc
    rho * x + C * x ^ 2 <= rho * x + C * r * x := add_le_add_left hquad (rho * x)
    _ = (rho + C * r) * x := by ring
    _ <= q * x := hlin

theorem invariant_ball_under_quadratic_stable_map
    (rho C r : ℝ)
    (x : ℕ → ℝ)
    (hC : 0 <= C)
    (hmargin : rho + C * r <= 1)
    (hx_nonneg : ∀ n, 0 <= x n)
    (hx0 : x 0 <= r)
    (hrec : ∀ n, x (n + 1) <= rho * x n + C * (x n) ^ 2) :
    ∀ n, x n <= r := by
  intro n
  induction n with
  | zero =>
      exact hx0
  | succ n ih =>
      have hstep : rho * x n + C * (x n) ^ 2 <= x n := by
        simpa using one_step_contraction_inside_ball
          rho C r 1 (x n) hC (hx_nonneg n) ih hmargin
      exact (hrec n).trans (hstep.trans ih)

#print axioms printed_closing_condition_impossible
#print axioms one_step_contraction_inside_ball
#print axioms invariant_ball_under_quadratic_stable_map

end Millennium.YangMills.FaizalShabirAppendixA10Firewall
