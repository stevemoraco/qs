import Mathlib

namespace Millennium.YangMills

/--
A scalar firewall for Kirk v4, Lemma 6.38, equations (94)--(96).

Abstract the nonnegative multiplicative branching factor in (95) by `A`.
If `A ≥ 1`, `J ≥ 0`, and the unit-ball admission inequality

  J * A - 1 ≤ 1

holds, then necessarily `J ≤ 2`.

Thus the statement in the source that the admission condition can be forced
merely because all small activity/physical rows tend to zero needs an
additional quantitative hypothesis on the junction constant (or a larger
branching ball with a correspondingly stronger incidence reserve).
-/
theorem unit_ball_admission_forces_junction_le_two
    (J A : ℝ)
    (hJ : 0 ≤ J)
    (hA : 1 ≤ A)
    (hadm : J * A - 1 ≤ 1) :
    J ≤ 2 := by
  have hJA : J ≤ J * A := by
    calc
      J = J * 1 := by ring
      _ ≤ J * A := mul_le_mul_of_nonneg_left hA hJ
  linarith

/--
More generally, if a rooted recursion with baseline junction constant `J`
is required to map into a branch ball of radius `B`, then any multiplicative
factor `A ≥ 1` forces the necessary baseline condition `J - 1 ≤ B`.
-/
theorem branch_ball_admission_forces_baseline_radius
    (J A B : ℝ)
    (hJ : 0 ≤ J)
    (hA : 1 ≤ A)
    (hadm : J * A - 1 ≤ B) :
    J - 1 ≤ B := by
  have hJA : J ≤ J * A := by
    calc
      J = J * 1 := by ring
      _ ≤ J * A := mul_le_mul_of_nonneg_left hA hJ
  linarith

/--
The smallest explicit hostile model: with junction constant `J = 3` and all
small rows set to zero, the multiplicative factor in (95) is exactly `A = 1`,
so the claimed unit-ball admission inequality fails.
-/
theorem junction_three_fails_unit_ball_at_zero_rows :
    ¬ ((3 : ℝ) * 1 - 1 ≤ 1) := by
  norm_num

#print axioms unit_ball_admission_forces_junction_le_two
#print axioms branch_ball_admission_forces_baseline_radius
#print axioms junction_three_fails_unit_ball_at_zero_rows

end Millennium.YangMills
