import Mathlib

/-!
# Yang--Mills absolute transfer-defect firewall: finite core

HONESTY BOUNDARY

This file verifies only scalar and finite rational identities used in the
accompanying source audit.  It does not formalize transfer operators, infinite
series, spectral calculus, Osterwalder--Schrader reconstruction, lattice gauge
theory, renormalization, compact gauge groups, or Yang--Mills.
-/

namespace Millennium
namespace YangMills
namespace AbsoluteDefectCountermodelFinite

/-- A positive initial number and a finite nonnegative loss do not imply a
    positive remainder. -/
theorem finite_total_loss_need_not_leave_positive_remainder :
    ∃ delta0 eps : ℝ,
      0 < delta0 ∧ 0 ≤ eps ∧ delta0 - eps ≤ 0 := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  norm_num

/-- A lower operator/form comparison cannot be read as the reverse upper
    comparison.  This scalar instance is the exact direction error. -/
theorem lower_bound_does_not_imply_corresponding_upper :
    ∃ next compressed remainder : ℝ,
      0 ≤ remainder ∧
      compressed - remainder ≤ next ∧
      ¬ next ≤ compressed + remainder := by
  refine ⟨1, 0, 0, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Nonnegativity of a physical gap does not bound the exponential conversion
    factor by the value at gap one. -/
theorem nonnegative_gap_does_not_bound_exponential_factor
    (a : ℝ) (ha : 0 < a) :
    ¬ (∀ delta : ℝ, 0 ≤ delta →
        Real.exp (a * delta) ≤ Real.exp a) := by
  intro h
  have hbad := h 2 (by norm_num)
  have harg : a < a * 2 := by nlinarith
  have hexp : Real.exp a < Real.exp (a * 2) :=
    Real.exp_lt_exp.mpr harg
  exact (not_lt_of_ge hbad) hexp

/-- If the transfer eigenvalue is held fixed while the physical time step is
    doubled, the generator gap is halved. -/
theorem same_transfer_doubled_time_halves_generator_gap
    (a q : ℝ) (ha : a ≠ 0) :
    (-Real.log q) / (2 * a) =
      (1 / 2 : ℝ) * ((-Real.log q) / a) := by
  field_simp
  ring

/-- The first four excited transfer eigenvalues in the exact countermodel. -/
theorem first_four_transfer_recursions :
    let r0 : ℚ := 1 / 2
    let r1 : ℚ := 1 / 4
    let r2 : ℚ := 1 / 8
    let r3 : ℚ := 1 / 16
    r1 = r0 ^ 2 + 0 ∧
    r2 = r1 ^ 2 + 1 / 16 ∧
    r3 = r2 ^ 2 + 3 / 64 := by
  norm_num

/-- The next defect is positive and the first nonzero defects are small in
    absolute norm. -/
theorem first_absolute_defect_budget :
    let eps0 : ℚ := 0
    let eps1 : ℚ := 1 / 16
    let eps2 : ℚ := 3 / 64
    let eps3 : ℚ := 7 / 256
    0 ≤ eps0 ∧ 0 ≤ eps1 ∧ 0 ≤ eps2 ∧ 0 ≤ eps3 ∧
    eps0 + eps1 + eps2 + eps3 = 35 / 256 ∧
    eps0 + eps1 + eps2 + eps3 < 1 / 6 := by
  norm_num

/-- The same small absolute defects are large relative to the squared excited
    eigenvalue: the first ratios are `0,1,3,7`. -/
theorem first_relative_defects :
    let r0 : ℚ := 1 / 2
    let r1 : ℚ := 1 / 4
    let r2 : ℚ := 1 / 8
    let r3 : ℚ := 1 / 16
    let eps0 : ℚ := 0
    let eps1 : ℚ := 1 / 16
    let eps2 : ℚ := 3 / 64
    let eps3 : ℚ := 7 / 256
    eps0 / r0 ^ 2 = 0 ∧
    eps1 / r1 ^ 2 = 1 ∧
    eps2 / r2 ^ 2 = 3 ∧
    eps3 / r3 ^ 2 = 7 := by
  norm_num

/-- The physical-gap coefficients for the first four scales are
    `1,1,3/4,1/2`; hence the transfer recursion does not keep the physical gap
    fixed. -/
theorem first_physical_gap_coefficients_drop :
    let c0 : ℚ := 1
    let c1 : ℚ := 1
    let c2 : ℚ := 3 / 4
    let c3 : ℚ := 1 / 2
    c0 = c1 ∧ c2 < c1 ∧ c3 < c2 := by
  norm_num

#print axioms finite_total_loss_need_not_leave_positive_remainder
#print axioms lower_bound_does_not_imply_corresponding_upper
#print axioms nonnegative_gap_does_not_bound_exponential_factor
#print axioms same_transfer_doubled_time_halves_generator_gap
#print axioms first_four_transfer_recursions
#print axioms first_absolute_defect_budget
#print axioms first_relative_defects
#print axioms first_physical_gap_coefficients_drop

end AbsoluteDefectCountermodelFinite
end YangMills
end Millennium
