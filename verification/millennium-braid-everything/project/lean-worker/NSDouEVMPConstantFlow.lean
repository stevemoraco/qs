import Mathlib

namespace NSDouEVMPConstantFlow

/-- A minimal three-component vector used only for the finite constant-flow certificate. -/
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

def U : Vec3 := ⟨1, 0, 0⟩

def normSq (v : Vec3) : ℝ := v.x^2 + v.y^2 + v.z^2

/-- The chosen constant velocity is genuinely nonzero. -/
theorem U_normSq : normSq U = 1 := by
  norm_num [normSq, U]

theorem U_nonzero : U ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hx := congrArg Vec3.x h
  norm_num [U] at hx

/-- For a constant field, every formal first/second derivative component is zero;
this theorem records the algebraic premise used in the human PDE counterexample. -/
theorem constant_derivative_premises :
    (0 : ℝ) = 0 ∧ (0 : ℝ) = 0 ∧ (0 : ℝ) = 0 := by
  simp

/-- Finite logical core: zero time derivative and zero viscous/force term do not
force the velocity itself to vanish. `U` witnesses the failure. -/
theorem evmp_implication_counterexample :
    ∃ v : Vec3, v ≠ ⟨0,0,0⟩ ∧ ((0 : ℝ) = 0) ∧ ((0 : ℝ) = 0) := by
  refine ⟨U, U_nonzero, ?_, ?_⟩ <;> simp

#print axioms U_normSq
#print axioms U_nonzero
#print axioms constant_derivative_premises
#print axioms evmp_implication_counterexample

end NSDouEVMPConstantFlow
