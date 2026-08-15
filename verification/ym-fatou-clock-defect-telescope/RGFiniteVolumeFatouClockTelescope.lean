import Mathlib

/-!
# Finite-volume Fatou-clock telescope

Finite algebra for the nonautonomous regulator-to-thermodynamic Lambda bridge.

If `psi n` is an exact thermodynamic Fatou coordinate evaluated along an actual
finite-volume/nonautonomous orbit and `delta n` is the one-step Abel defect,

`psi (n+1) = psi n - 1 + delta n`,

then the cumulative clock error is exactly the finite sum of the defects.
A uniform bound on that signed cumulative defect therefore gives a uniform
additive clock window.

This file does not prove any Yang--Mills RG estimate, identify Kirk's finite-
volume defects, construct a physical mass gap, or prove a Millennium theorem.
-/

namespace Millennium.YangMills.RGFiniteVolumeFatouClockTelescope

open Finset

/-- Exact telescoping of one-step nonautonomous defects in an Abel/Fatou clock. -/
theorem fatou_clock_telescope
    (psi delta : ℕ → ℝ)
    (hstep : ∀ n : ℕ, psi (n + 1) = psi n - 1 + delta n) :
    ∀ N : ℕ,
      psi N = psi 0 - (N : ℝ) + ∑ j ∈ Finset.range N, delta j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [hstep N, ih, Finset.sum_range_succ]
      push_cast
      ring

/-- The deviation from the ideal unit-speed Fatou clock is exactly the signed
cumulative one-step defect. -/
theorem fatou_clock_error_eq_sum
    (psi delta : ℕ → ℝ)
    (hstep : ∀ n : ℕ, psi (n + 1) = psi n - 1 + delta n)
    (N : ℕ) :
    psi N - (psi 0 - (N : ℝ)) = ∑ j ∈ Finset.range N, delta j := by
  rw [fatou_clock_telescope psi delta hstep N]
  ring

/-- A regulator-independent bound on the signed cumulative defect gives the
same regulator-independent additive window for the exact Fatou clock. -/
theorem fatou_clock_error_le_of_signed_sum_le
    (psi delta : ℕ → ℝ)
    (hstep : ∀ n : ℕ, psi (n + 1) = psi n - 1 + delta n)
    (N : ℕ) (W : ℝ)
    (hW : |∑ j ∈ Finset.range N, delta j| ≤ W) :
    |psi N - (psi 0 - (N : ℝ))| ≤ W := by
  rw [fatou_clock_error_eq_sum psi delta hstep N]
  exact hW

/-- Absolute stepwise control is sufficient but stronger than necessary: it
implies the corresponding signed cumulative clock bound by the triangle
inequality. -/
theorem signed_sum_le_sum_abs
    (delta : ℕ → ℝ) (N : ℕ) :
    |∑ j ∈ Finset.range N, delta j| ≤ ∑ j ∈ Finset.range N, |delta j| := by
  simpa using Finset.abs_sum_le_sum_abs (s := Finset.range N) delta

#print axioms fatou_clock_telescope
#print axioms fatou_clock_error_eq_sum
#print axioms fatou_clock_error_le_of_signed_sum_le
#print axioms signed_sum_le_sum_abs

end Millennium.YangMills.RGFiniteVolumeFatouClockTelescope
