import Mathlib

/-!
# Faizal–Shabir terminal-entry stability firewall

Finite scalar logic for the ultraviolet-stability recurrence used upstream of
the fixed-physical-scale clustering repair.

This file deliberately does **not** formalize the Yang–Mills RG map, polymer
norms, FRD, BKAR, continuum OS reconstruction, or a mass gap.  It checks only
three load-bearing scalar facts:

1. the printed condition `C * eps <= eps / 2` cannot be achieved merely by
   making `eps` smaller; for positive `eps` it forces `C <= 1/2`;
2. a finite additive forcing budget need not keep the first step inside an
   arbitrarily small ball;
3. after an independently proved entry into a radius-`r` ball, the quadratic
   recurrence is forward invariant if the *tail* forcing is uniformly small.
-/

namespace Millennium.YangMills.FaizalShabirTerminalEntryFirewall

theorem printed_epsilon_condition_forces_half_bound
    (C eps : ℝ)
    (heps : 0 < eps)
    (h : C * eps <= eps / 2) :
    C <= (1 : ℝ) / 2 := by
  nlinarith

theorem finite_forcing_can_break_small_ball
    (C eps : ℝ)
    (hsmall : 2 * eps < C) :
    let x0 : ℝ := 0
    let delta0 : ℝ := 1
    let x1 : ℝ := C * x0 ^ 2 + C * delta0
    2 * eps < x1 := by
  dsimp
  nlinarith

theorem invariant_ball_under_small_tail
    (C r : ℝ)
    (x delta : ℕ → ℝ)
    (hC : 0 <= C)
    (hr : 0 <= r)
    (hCr : C * r <= (1 : ℝ) / 2)
    (hx_nonneg : ∀ n, 0 <= x n)
    (hx0 : x 0 <= r)
    (hdelta : ∀ n, C * delta n <= r / 2)
    (hrec : ∀ n, x (n + 1) <= C * (x n) ^ 2 + C * delta n) :
    ∀ n, x n <= r := by
  intro n
  induction n with
  | zero =>
      exact hx0
  | succ n ih =>
      have hxn0 : 0 <= x n := hx_nonneg n
      have hsq : (x n) ^ 2 <= r ^ 2 := by
        nlinarith
      have hCsq : C * (x n) ^ 2 <= C * r ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hC
      have hmul := mul_le_mul_of_nonneg_right hCr hr
      have hCr2 : C * r ^ 2 <= r / 2 := by
        nlinarith [hmul]
      calc
        x (n + 1) <= C * (x n) ^ 2 + C * delta n := hrec n
        _ <= r / 2 + r / 2 := add_le_add (hCsq.trans hCr2) (hdelta n)
        _ = r := by ring

#print axioms printed_epsilon_condition_forces_half_bound
#print axioms finite_forcing_can_break_small_ball
#print axioms invariant_ball_under_small_tail

end Millennium.YangMills.FaizalShabirTerminalEntryFirewall
