import Mathlib

/-!
# Temporal cone-axis drift firewall

Finite real algebra only.

The intended PDE use is external. If a high-vorticity direction is close to a
same-time axis and that axis is close to one fixed late-time axis, then the
vorticity direction lies in one fixed strict cone. Conversely, escape from that
cone while the same-time spatial defect remains small forces temporal axis drift.

This file does not formalize vector geometry, Lei–Ren–Tian, Pineau–Vicol, Yu,
vorticity, Navier–Stokes, or a Clay statement.
-/

namespace NSAnchorTemporalConeBudget

/-- Same-time direction error plus temporal axis drift bounds fixed-axis error. -/
theorem local_plus_axis_drift
    (local drift pair alpha beta : ℝ)
    (hpair : pair ≤ local + drift)
    (hlocal : local ≤ alpha)
    (hdrift : drift ≤ beta) :
    pair ≤ alpha + beta := by
  linarith

/-- A strict total error budget leaves a positive fixed-cone margin. -/
theorem strict_cone_margin
    (alpha beta : ℝ)
    (hmargin : alpha + beta < 1) :
    0 < 1 - (alpha + beta) := by
  linarith

/-- Package the fixed-axis direction bound together with its strict margin. -/
theorem fixed_axis_cone_budget
    (local drift pair alpha beta : ℝ)
    (hpair : pair ≤ local + drift)
    (hlocal : local ≤ alpha)
    (hdrift : drift ≤ beta)
    (hmargin : alpha + beta < 1) :
    pair ≤ alpha + beta ∧ 0 < 1 - (alpha + beta) := by
  exact ⟨local_plus_axis_drift local drift pair alpha beta hpair hlocal hdrift,
    strict_cone_margin alpha beta hmargin⟩

/-- If the fixed-axis error escapes `alpha + beta` while the same-time defect is
at most `alpha`, then the axis itself must have drifted by more than `beta`. -/
theorem cone_escape_forces_axis_drift
    (local drift pair alpha beta : ℝ)
    (hpair : pair ≤ local + drift)
    (hlocal : local ≤ alpha)
    (hescape : alpha + beta < pair) :
    beta < drift := by
  linarith

#print axioms local_plus_axis_drift
#print axioms strict_cone_margin
#print axioms fixed_axis_cone_budget
#print axioms cone_escape_forces_axis_drift

end NSAnchorTemporalConeBudget
