import Mathlib

/-!
# Yang--Mills OS transfer audit: finite obstruction cores

Honesty status: elementary scalar and quadratic-form mathematics only. This file
formalizes finite logical cores from an audit of Osterwalder--Schrader transfer
arguments. It does not formalize Yang--Mills theory, OS reconstruction,
continuum limits, gauge invariance, or any official Millennium statement.
-/

namespace MillenniumBraid
namespace YMOsterwalderSchrader

/-- Scalar spectral core: a nonnegative isometry has only eigenvalue `1`. -/
theorem positive_isometry_scalar_trivial
    (t : ℝ) (ht : 0 ≤ t) (hiso : t ^ 2 = 1) : t = 1 := by
  nlinarith

/-- A lower order bound does not imply the upper estimate needed for Rayleigh--Ritz. -/
theorem lower_order_bound_does_not_give_upper_control :
    ∃ A B ε : ℝ,
      0 ≤ ε ∧ A - ε ≤ B ∧ ¬ B ≤ A + ε := by
  refine ⟨0, 2, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-- A difference of two nonnegative squared norms can be negative. -/
theorem difference_of_nonnegative_squares_can_be_negative :
    ∃ x y : ℝ,
      0 ≤ x ^ 2 ∧ 0 ≤ y ^ 2 ∧ x ^ 2 - y ^ 2 < 0 := by
  refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Entrywise nonnegative symmetric kernels need not be positive semidefinite. -/
theorem nonnegative_symmetric_kernel_need_not_be_psd :
    ∃ a b c x y : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 < 0 := by
  refine ⟨0, 1, 0, 1, -1, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Exact scale covariance of the mass numerator at a fixed physical time. -/
theorem fixed_physical_time_mass_numerator
    (τ m : ℝ) :
    -Real.log (Real.exp (-τ * m)) = τ * m := by
  rw [Real.log_exp]
  ring

/-- A fixed one-step contraction forces energy of order `1 / a`. -/
theorem fixed_half_step_contraction_forces_large_energy
    (a M : ℝ) (ha : 0 < a) (hM : 0 < M)
    (hscale : a ≤ Real.log 2 / M) :
    M ≤ Real.log 2 / a := by
  have hmul : a * M ≤ Real.log 2 := (le_div_iff₀ hM).mp hscale
  apply (le_div_iff₀ ha).2
  nlinarith

#print axioms positive_isometry_scalar_trivial
#print axioms lower_order_bound_does_not_give_upper_control
#print axioms difference_of_nonnegative_squares_can_be_negative
#print axioms nonnegative_symmetric_kernel_need_not_be_psd
#print axioms fixed_physical_time_mass_numerator
#print axioms fixed_half_step_contraction_forces_large_energy

end YMOsterwalderSchrader
end MillenniumBraid
