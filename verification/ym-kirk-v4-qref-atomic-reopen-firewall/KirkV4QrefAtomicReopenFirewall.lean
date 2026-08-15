import Mathlib

namespace Millennium.YangMills

/-!
# Kirk v4 Qref atomic-reopen firewalls

Two finite counterexamples behind the source audit of the proposed
`YM-KIRK-QREF-ATOMIC-REOPEN` repair.

1. Being quadratic in two normal-field variables does not imply dependence on
   only two compact pivot variables.  The coefficient of a quadratic monomial
   may depend simultaneously on arbitrarily many compact variables.  The
   four-pivot toy below is already enough to refute the inference
   "two-jet => at most two pivots".

2. A norm bound after exact collection does not, by itself, bound the absolute
   norm sum after reopening collected terms: cancellation can make the
   collected norm zero while the atomic norm sum is arbitrarily large.

These are finite logical firewalls only.  They do not assert that Kirk's actual
reference factors realize either hostile model.  A repair remains possible if
one proves, from the pre-collect construction, compact-coefficient locality and
an absolutely summable marked atomic row before pivot classification.
-/

def fourPivotQuadratic
    (x y p₁ p₂ p₃ p₄ : ℝ) : ℝ :=
  x * y * p₁ * p₂ * p₃ * p₄

theorem four_pivot_quadratic_nonzero :
    fourPivotQuadratic 1 1 1 1 1 1 = 1 := by
  norm_num [fourPivotQuadratic]

theorem four_pivot_quadratic_each_pivot_essential :
    fourPivotQuadratic 1 1 0 1 1 1 = 0 ∧
    fourPivotQuadratic 1 1 1 0 1 1 = 0 ∧
    fourPivotQuadratic 1 1 1 1 0 1 = 0 ∧
    fourPivotQuadratic 1 1 1 1 1 0 = 0 := by
  norm_num [fourPivotQuadratic]

theorem atomic_reopen_cancellation_firewall
    (M : ℝ) (hM : 0 ≤ M) :
    |M + (-M)| = 0 ∧ |M| + |-M| = 2 * M := by
  constructor
  · simp
  · rw [abs_of_nonneg hM, abs_neg, abs_of_nonneg hM]
    ring

theorem collected_bound_does_not_control_atomic_sum
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ x y : ℝ, |x + y| ≤ C ∧ C < |x| + |y| := by
  refine ⟨C + 1, -(C + 1), ?_, ?_⟩
  · simpa using hC
  · have hCp : 0 ≤ C + 1 := by linarith
    rw [abs_of_nonneg hCp, abs_neg, abs_of_nonneg hCp]
    linarith

#print axioms four_pivot_quadratic_nonzero
#print axioms four_pivot_quadratic_each_pivot_essential
#print axioms atomic_reopen_cancellation_firewall
#print axioms collected_bound_does_not_control_atomic_sum

end Millennium.YangMills
