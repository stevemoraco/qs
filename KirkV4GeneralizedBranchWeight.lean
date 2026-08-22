import Mathlib

namespace Millennium.YangMills

/-- The generalized value branch weight is dominated by one fixed geometric
incidence weight. -/
theorem generalized_branch_value_weight_le
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    (1 + B) ^ (n - 1) ≤ (2 * (1 + B)) ^ n := by
  have hq1 : 1 ≤ 1 + B := by linarith
  have hq0 : 0 ≤ 1 + B := by linarith
  calc
    (1 + B) ^ (n - 1) ≤ (1 + B) ^ n :=
      pow_le_pow_right₀ hq1 (Nat.sub_le n 1)
    _ ≤ (2 * (1 + B)) ^ n := by
      apply pow_le_pow_left₀ hq0
      nlinarith

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      omega

/-- The generalized derivative branch weight is dominated by the same fixed
geometric incidence weight. -/
theorem generalized_branch_derivative_weight_le
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    ((n - 1 : ℕ) : ℝ) * (1 + B) ^ (n - 2) ≤
      (2 * (1 + B)) ^ n := by
  have hq1 : 1 ≤ 1 + B := by linarith
  have hq0 : 0 ≤ 1 + B := by linarith
  have hnNat : n - 1 ≤ 2 ^ n :=
    le_trans (Nat.sub_le n 1) (nat_le_two_pow n)
  have hn : ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hnNat
  have hp : (1 + B) ^ (n - 2) ≤ (1 + B) ^ n :=
    pow_le_pow_right₀ hq1 (Nat.sub_le n 2)
  calc
    ((n - 1 : ℕ) : ℝ) * (1 + B) ^ (n - 2) ≤
        (2 : ℝ) ^ n * (1 + B) ^ (n - 2) := by
      gcongr
    _ ≤ (2 : ℝ) ^ n * (1 + B) ^ n := by
      gcongr
    _ = (2 * (1 + B)) ^ n := by
      rw [mul_pow]

/-- One conjunction suitable for applying an arbitrary-incidence-charge row. -/
theorem generalized_branch_weights_share_one_charge
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    (1 + B) ^ (n - 1) ≤ (2 * (1 + B)) ^ n ∧
    ((n - 1 : ℕ) : ℝ) * (1 + B) ^ (n - 2) ≤
      (2 * (1 + B)) ^ n := by
  exact ⟨generalized_branch_value_weight_le B hB n,
    generalized_branch_derivative_weight_le B hB n⟩

#print axioms generalized_branch_value_weight_le
#print axioms generalized_branch_derivative_weight_le
#print axioms generalized_branch_weights_share_one_charge

end Millennium.YangMills
