import Mathlib

namespace NSEndpointFirewalls

/-- Pointwise quotient saturation does not imply the cubic-vs-quadratic Euler identity. -/
theorem saturation_does_not_force_euler_identity :
    ∃ (J A Lambda : ℝ),
      0 < Lambda ∧ A = 1 ∧ J = Lambda * A ∧
      3 * J ≠ 2 * Lambda * A := by
  refine ⟨1, 1, 1, by norm_num, rfl, by norm_num, ?_⟩
  norm_num

/-- Cubic transfer divided by quadratic visibility scales linearly with amplitude. -/
theorem cubic_over_quadratic_amplitude_quotient
    (a : ℝ) (ha : 0 < a) :
    a ^ 3 / a ^ 2 = a := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  apply (div_eq_iff ha2).2
  ring

/-- Hence the cubic/quadratic quotient is unbounded above on positive amplitudes. -/
theorem cubic_over_quadratic_quotient_unbounded
    (M : ℝ) : ∃ a : ℝ, 0 < a ∧ M < a ^ 3 / a ^ 2 := by
  let a : ℝ := max (M + 1) 1
  have ha : 0 < a := by
    dsimp [a]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨a, ha, ?_⟩
  rw [cubic_over_quadratic_amplitude_quotient a ha]
  dsimp [a]
  have hM : M < M + 1 := by linarith
  exact lt_of_lt_of_le hM (le_max_left _ _)

/-- Scalar model of the exact amplitude residual for a linear-plus-quadratic equation. -/
theorem quadratic_equation_amplitude_residual
    (L B u a : ℝ)
    (hsol : L * u + B * u ^ 2 = 0) :
    L * (a * u) + B * (a * u) ^ 2 =
      (a * (a - 1)) * (B * u ^ 2) := by
  have hLu : L * u = -(B * u ^ 2) := by linarith
  calc
    L * (a * u) + B * (a * u) ^ 2
        = a * (L * u) + a ^ 2 * (B * u ^ 2) := by ring
    _ = a * (-(B * u ^ 2)) + a ^ 2 * (B * u ^ 2) := by rw [hLu]
    _ = (a * (a - 1)) * (B * u ^ 2) := by ring

/-- A nontrivial pure amplitude scaling therefore generally leaves the same quadratic solution class. -/
theorem nontrivial_amplitude_scaling_leaves_quadratic_solution_class
    (L B u a : ℝ)
    (hsol : L * u + B * u ^ 2 = 0)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hquad : B * u ^ 2 ≠ 0) :
    L * (a * u) + B * (a * u) ^ 2 ≠ 0 := by
  rw [quadratic_equation_amplitude_residual L B u a hsol]
  have haa : a * (a - 1) ≠ 0 :=
    mul_ne_zero ha0 (sub_ne_zero.mpr ha1)
  exact mul_ne_zero haa hquad

#print axioms saturation_does_not_force_euler_identity
#print axioms cubic_over_quadratic_amplitude_quotient
#print axioms cubic_over_quadratic_quotient_unbounded
#print axioms quadratic_equation_amplitude_residual
#print axioms nontrivial_amplitude_scaling_leaves_quadratic_solution_class

end NSEndpointFirewalls
