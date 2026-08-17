import Mathlib

/-!
# Faizal--Shabir complement-max step firewall

Finite real-algebra firewall for the inference from equations (6.47) to (6.48)
in the detailed multiscale argument of arXiv:2606.19362v1.

The displayed estimate has the shape

  x - e <= y <= max x c + e,

with `c = 1 - delta`.  This does not imply `|y-x| <= e` unless the visible
spectral edge already dominates the complement ceiling (`c <= x`) or another
argument removes the max branch.

This file formalizes the exact counterexample and the repaired one-step theorem.
It does not formalize transfer operators, Yang--Mills theory, OS reconstruction,
or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirComplementMaxStepFirewall

/-- Exact counterexample to dropping the complement `max` branch: with zero
error, the two-sided estimate permits an upward jump from `0` to `1/2`. -/
theorem complement_max_bound_does_not_imply_absolute_step_bound :
    ∃ x y c e : ℝ,
      0 ≤ e ∧
      x - e ≤ y ∧
      y ≤ max x c + e ∧
      ¬ |y - x| ≤ e := by
  refine ⟨0, (1 : ℝ) / 2, (1 : ℝ) / 2, 0, ?_⟩
  norm_num

/-- Once the visible spectral value is at least the complement ceiling, the
max branch collapses and the desired absolute one-step estimate follows. -/
theorem complement_max_step_repair
    (x y c e : ℝ)
    (hc : c ≤ x)
    (hlower : x - e ≤ y)
    (hupper : y ≤ max x c + e) :
    |y - x| ≤ e := by
  have hmax : max x c = x := max_eq_left hc
  have hyupper : y - x ≤ e := by
    rw [hmax] at hupper
    linarith
  have hylower : -e ≤ y - x := by
    linarith
  exact abs_le.mpr ⟨hylower, hyupper⟩

/-- The same repair with the paper's factor-three error budget. -/
theorem complement_max_step_repair_three
    (x y c ε : ℝ)
    (hc : c ≤ x)
    (hlower : x - 3 * ε ≤ y)
    (hupper : y ≤ max x c + 3 * ε) :
    |y - x| ≤ 3 * ε := by
  exact complement_max_step_repair x y c (3 * ε) hc hlower hupper

#print axioms complement_max_bound_does_not_imply_absolute_step_bound
#print axioms complement_max_step_repair
#print axioms complement_max_step_repair_three

end Millennium.YangMills.FaizalShabirComplementMaxStepFirewall
