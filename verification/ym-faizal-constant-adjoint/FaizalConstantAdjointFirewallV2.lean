import Mathlib

namespace Millennium.YangMills.FaizalConstantAdjointFirewallV2

theorem covariant_defect_zero_iff_fixed
    {V : Type*} [AddGroup V] (A : V → V) (v : V) :
    A v - v = 0 ↔ A v = v := by
  exact sub_eq_zero

def halfTurn (v : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (-v.1, (-v.2.1, v.2.2))

def witness : ℝ × (ℝ × ℝ) := (1, (0, 0))

theorem halfTurn_involutive : Function.Involutive halfTurn := by
  intro v
  rcases v with ⟨x, y, z⟩
  simp [halfTurn]

theorem halfTurn_preserves_sqNorm (v : ℝ × (ℝ × ℝ)) :
    (halfTurn v).1 ^ 2 + (halfTurn v).2.1 ^ 2 + (halfTurn v).2.2 ^ 2 =
      v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  simp [halfTurn]

theorem witness_not_fixed : halfTurn witness ≠ witness := by
  norm_num [halfTurn, witness]

theorem witness_defect :
    halfTurn witness - witness = ((-2 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
  norm_num [halfTurn, witness]

theorem constant_not_covariantly_constant : halfTurn witness - witness ≠ 0 := by
  rw [witness_defect]
  norm_num

theorem constancy_does_not_force_kernel :
    ∃ (A : (ℝ × (ℝ × ℝ)) → (ℝ × (ℝ × ℝ))) (v : ℝ × (ℝ × ℝ)),
      Function.Involutive A ∧
      (∀ w,
        (A w).1 ^ 2 + (A w).2.1 ^ 2 + (A w).2.2 ^ 2 =
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2) ∧
      A v - v ≠ 0 := by
  exact ⟨halfTurn, witness, halfTurn_involutive,
    halfTurn_preserves_sqNorm, constant_not_covariantly_constant⟩

#print axioms covariant_defect_zero_iff_fixed
#print axioms halfTurn_involutive
#print axioms halfTurn_preserves_sqNorm
#print axioms witness_not_fixed
#print axioms witness_defect
#print axioms constant_not_covariantly_constant
#print axioms constancy_does_not_force_kernel

end Millennium.YangMills.FaizalConstantAdjointFirewallV2
