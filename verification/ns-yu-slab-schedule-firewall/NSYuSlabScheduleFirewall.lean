import Mathlib

/-!
# Yu short-slab scheduling firewall

Finite algebra only.  These theorems formalize the no-free-lunch statements used
in the current audit of logarithmic time-slab scheduling for the filtered
Navier--Stokes localization shell budgets.

They do **not** formalize Yu's PDE estimates, Navier--Stokes, summability of any
actual shell budget, or a Millennium Prize conclusion.
-/

namespace NSYuSlabScheduleFirewall

/-- If a retained signal and a shell cost are both proportional to the same
slab fraction, changing that fraction creates no relative gain. -/
theorem proportional_single (signalRate shellRate theta : ℝ) :
    shellRate * (signalRate * theta) =
      signalRate * (shellRate * theta) := by
  ring

/-- The same proportionality survives every finite schedule. -/
theorem proportional_finite_schedule
    {ι : Type*} [Fintype ι]
    (signalRate shellRate : ℝ) (theta : ι → ℝ) :
    shellRate * (∑ i, signalRate * theta i) =
      signalRate * (∑ i, shellRate * theta i) := by
  calc
    shellRate * (∑ i, signalRate * theta i) =
        ∑ i, shellRate * (signalRate * theta i) := by
          rw [Finset.mul_sum]
    _ = ∑ i, signalRate * (shellRate * theta i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = signalRate * (∑ i, shellRate * theta i) := by
          rw [Finset.mul_sum]

/-- If both quantities scale linearly in a positive slab length, obtaining a
strict shell-to-signal ratio requires a genuine constant gap; time refinement
alone cannot manufacture it. -/
theorem strict_ratio_requires_constant_gap
    (signalRate shellRate theta q : ℝ)
    (htheta : 0 < theta)
    (h : shellRate * theta ≤ q * (signalRate * theta)) :
    shellRate ≤ q * signalRate := by
  exact (mul_le_mul_right htheta).mp (by
    simpa [mul_assoc] using h)

/-- Aggregate signal and shell totals alone do not force one of two slabs to be
simultaneously signal-rich and shell-poor.  The entire signal and shell cost can
sit in the same slab. -/
theorem concentrated_two_slab_no_balanced_selection :
    ¬ (((1 : ℝ) ≥ 1 / 2 ∧ (1 : ℝ) ≤ 1 / 2) ∨
       ((0 : ℝ) ≥ 1 / 2 ∧ (0 : ℝ) ≤ 1 / 2)) := by
  norm_num

/-- The preceding countermodel can be phrased with named signal and shell
coordinates: both totals equal one, yet neither slab simultaneously carries at
least half the signal and at most half the shell cost. -/
theorem concentrated_two_slab_totals_and_failure :
    let signal₀ : ℝ := 1
    let signal₁ : ℝ := 0
    let shell₀ : ℝ := 1
    let shell₁ : ℝ := 0
    signal₀ + signal₁ = 1 ∧
    shell₀ + shell₁ = 1 ∧
    ¬ ((signal₀ ≥ 1 / 2 ∧ shell₀ ≤ 1 / 2) ∨
       (signal₁ ≥ 1 / 2 ∧ shell₁ ≤ 1 / 2)) := by
  norm_num

#print axioms proportional_single
#print axioms proportional_finite_schedule
#print axioms strict_ratio_requires_constant_gap
#print axioms concentrated_two_slab_no_balanced_selection
#print axioms concentrated_two_slab_totals_and_failure

end NSYuSlabScheduleFirewall
