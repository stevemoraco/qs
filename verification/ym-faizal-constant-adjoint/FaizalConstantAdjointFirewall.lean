import Mathlib

/-!
# Faizal--Shabir constant-adjoint-field firewall

Finite algebraic core for the hostile audit of arXiv:2606.19362v1,
`Reflection-Positive Construction of a Four-Dimensional SU(N) Yang-Mills Theory
with Mass Gap and Confinement`.

The paper defines a covariant forward difference of an adjoint field by

`∇⁺ φ = Ad(U) (φ at the next site) - φ at the current site`

and then repeatedly uses the claim that an ordinary site-constant adjoint field
is automatically in the kernel.  Algebraically, a constant field has zero
covariant difference only when its value is fixed by the relevant adjoint
holonomy.  Constancy alone is insufficient.

`halfTurnAdjoint` is the exact real-coordinate shadow of a nontrivial SU(2)
adjoint half-turn: it flips the two directions orthogonal to a Cartan axis and
fixes that axis.  A constant vector in a flipped direction has nonzero
covariant defect.

This file is a finite logical/operator firewall only.  It does not formalize
SU(2), the Faddeev--Popov operator, the fundamental modular region, OS
reconstruction, or Yang--Mills itself.
-/

namespace Millennium.YangMills.FaizalConstantAdjointFirewall

/-- For a constant field value `v`, the covariant forward difference
`AdU v - v` vanishes exactly when `v` is fixed by the adjoint action. -/
theorem constant_covariant_difference_eq_zero_iff_fixed
    {V : Type*} [AddGroup V] (AdU : V → V) (v : V) :
    AdU v - v = 0 ↔ AdU v = v := by
  exact sub_eq_zero

/-- Coordinate model of a half-turn in the adjoint representation: two axes
change sign and one axis is fixed. -/
def halfTurnAdjoint (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-v.1, -v.2.1, v.2.2)

/-- A constant adjoint-field value in a rotated direction. -/
def witness : ℝ × ℝ × ℝ := (1, 0, 0)

/-- The half-turn is genuinely involutive, as an adjoint action of an order-two
rotation should be. -/
theorem halfTurnAdjoint_involutive : Function.Involutive halfTurnAdjoint := by
  intro v
  rcases v with ⟨x, y, z⟩
  simp [halfTurnAdjoint]

/-- The half-turn preserves the Euclidean quadratic form. -/
theorem halfTurnAdjoint_preserves_sqNorm (v : ℝ × ℝ × ℝ) :
    (halfTurnAdjoint v).1 ^ 2 + (halfTurnAdjoint v).2.1 ^ 2 +
        (halfTurnAdjoint v).2.2 ^ 2 =
      v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  simp [halfTurnAdjoint]

/-- The chosen constant value is not fixed by the nontrivial adjoint action. -/
theorem witness_not_fixed : halfTurnAdjoint witness ≠ witness := by
  norm_num [halfTurnAdjoint, witness]

/-- Exact defect: an ordinary constant field can have a nonzero covariant
forward difference. -/
theorem witness_covariant_defect :
    halfTurnAdjoint witness - witness = (-2, 0, 0) := by
  norm_num [halfTurnAdjoint, witness]

/-- Therefore ordinary constancy does not imply covariant constancy, even for
an involutive norm-preserving adjoint-style action. -/
theorem constant_field_not_covariantly_constant :
    halfTurnAdjoint witness - witness ≠ 0 := by
  rw [witness_covariant_defect]
  norm_num

/-- Packaged countermodel to the inference `constant ⇒ covariant difference = 0`. -/
theorem constant_does_not_force_covariant_kernel :
    ∃ (AdU : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)) (v : ℝ × ℝ × ℝ),
      Function.Involutive AdU ∧
      (∀ w,
        (AdU w).1 ^ 2 + (AdU w).2.1 ^ 2 + (AdU w).2.2 ^ 2 =
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2) ∧
      AdU v - v ≠ 0 := by
  exact ⟨halfTurnAdjoint, witness, halfTurnAdjoint_involutive,
    halfTurnAdjoint_preserves_sqNorm, constant_field_not_covariantly_constant⟩

#print axioms constant_covariant_difference_eq_zero_iff_fixed
#print axioms halfTurnAdjoint_involutive
#print axioms halfTurnAdjoint_preserves_sqNorm
#print axioms witness_not_fixed
#print axioms witness_covariant_defect
#print axioms constant_field_not_covariantly_constant
#print axioms constant_does_not_force_covariant_kernel

end Millennium.YangMills.FaizalConstantAdjointFirewall
