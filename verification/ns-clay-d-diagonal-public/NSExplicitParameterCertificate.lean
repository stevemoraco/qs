import Mathlib

namespace NSExplicitParameterCertificate

theorem explicit_parameter_checkpoint :
    let α : ℝ := 9 / 4
    let b : ℝ := 11 / 10
    let βshell : ℝ := 89 / 40
    let βloc : ℝ := 5 / 6
    let s : ℝ := 1 / 20
    1 < b ∧ b < α / 2 ∧ 2 * b < βshell ∧ α - s < βshell ∧ βshell < α ∧
    βloc = 2 * (α - 1) / 3 ∧ b * βloc < 1 ∧ α - βshell = 1 / 40 := by
  norm_num

theorem explicit_small_parameter_exponents :
    let α : ℝ := 9 / 4
    let b : ℝ := 11 / 10
    let βloc : ℝ := 2 * (α - 1) / 3
    1 - βloc = 1 / 6 ∧ 1 - b * βloc = 1 / 12 := by
  norm_num

theorem explicit_positive_regularization_gap :
    (0 : ℝ) < (1 / 20 : ℝ) - 1 / 40 := by
  norm_num

#print axioms explicit_parameter_checkpoint
#print axioms explicit_small_parameter_exponents
#print axioms explicit_positive_regularization_gap

end NSExplicitParameterCertificate
