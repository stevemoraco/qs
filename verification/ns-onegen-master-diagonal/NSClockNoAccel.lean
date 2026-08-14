import Mathlib

/-!
# AO generation-clock nonacceleration finite core

This file formalizes only the elementary recursion consequence used by the
curvature-versus-clock firewall: if each generation's clock proxy is no larger
than the initial clock proxy, its usable rate is bounded by a fixed multiple of
that proxy, and each activation consumes a fixed positive number of e-folds,
then every generation has a uniform positive duration lower bound.

It does NOT formalize the AO PDE modulation equations, the identification of
the clock proxy with `sqrt b`, any infinite Navier--Stokes cascade, or a Clay
statement.
-/

namespace Millennium.NavierStokes.ClockNoAccel

/-- A nonincreasing positive clock proxy and a rate bounded by `C * clock`
force a uniform lower bound on the time required to spend `L` e-folds. -/
theorem generation_time_lower_bound
    (clock rate duration : ℕ → ℝ)
    (C L : ℝ)
    (hC : 0 < C)
    (hL : 0 < L)
    (hclock : ∀ j, 0 < clock j ∧ clock j ≤ clock 0)
    (hrate : ∀ j, 0 < rate j ∧ rate j ≤ C * clock j)
    (hduration : ∀ j, L / rate j ≤ duration j) :
    ∀ j, L / (C * clock 0) ≤ duration j := by
  intro j
  have hc0 : 0 < clock 0 := (hclock 0).1
  have hden0 : 0 < C * clock 0 := mul_pos hC hc0
  have hrj : 0 < rate j := (hrate j).1
  have hrate0 : rate j ≤ C * clock 0 := by
    calc
      rate j ≤ C * clock j := (hrate j).2
      _ ≤ C * clock 0 := mul_le_mul_of_nonneg_left (hclock j).2 (le_of_lt hC)
  have hdiv : L / (C * clock 0) ≤ L / rate j := by
    apply (div_le_div_iff₀ hden0 hrj).2
    nlinarith
  exact hdiv.trans (hduration j)

/-- Every finite partial sum of generation durations is at least the number of
generations times the same positive lower bound. -/
theorem partial_sum_lower_bound
    (clock rate duration : ℕ → ℝ)
    (C L : ℝ)
    (hC : 0 < C)
    (hL : 0 < L)
    (hclock : ∀ j, 0 < clock j ∧ clock j ≤ clock 0)
    (hrate : ∀ j, 0 < rate j ∧ rate j ≤ C * clock j)
    (hduration : ∀ j, L / rate j ≤ duration j)
    (N : ℕ) :
    (N : ℝ) * (L / (C * clock 0)) ≤
      ∑ j ∈ Finset.range N, duration j := by
  have hpoint := generation_time_lower_bound
    clock rate duration C L hC hL hclock hrate hduration
  have hsum :
      ∑ j ∈ Finset.range N, (L / (C * clock 0)) ≤
        ∑ j ∈ Finset.range N, duration j := by
    exact Finset.sum_le_sum fun j _ => hpoint j
  simpa using hsum

#print axioms generation_time_lower_bound
#print axioms partial_sum_lower_bound

end Millennium.NavierStokes.ClockNoAccel
