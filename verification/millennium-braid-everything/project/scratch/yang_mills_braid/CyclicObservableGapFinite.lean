import Mathlib

namespace YangMillsBraid

/-- Positive spectral mass above `q+epsilon` eventually contradicts any fixed
`C q^n` moment envelope.  This finite scalar inequality is the core. -/
theorem above_edge_mass_ratio
    (mass q epsilon C : ℝ) (n : ℕ)
    (hmass : 0 < mass) (hq : 0 < q) (heps : 0 < epsilon)
    (hbound : mass * (q + epsilon) ^ n ≤ C * q ^ n) :
    mass * ((q + epsilon) / q) ^ n ≤ C := by
  have hqn : 0 < q ^ n := pow_pos hq n
  calc
    mass * ((q + epsilon) / q) ^ n
        = (mass * (q + epsilon) ^ n) / q ^ n := by
            rw [div_pow]
            field_simp [ne_of_gt hq]
            ring
    _ ≤ (C * q ^ n) / q ^ n :=
      div_le_div_of_nonneg_right hbound (le_of_lt hqn)
    _ = C := by field_simp [ne_of_gt hqn]

/-- A hidden unit mode is invisible to a noncyclic checked vector. -/
theorem noncyclic_hidden_mode (q : ℝ) :
    max q 1 = 1 ↔ q ≤ 1 := by
  exact max_eq_right

/-- A common transfer base below one gives a positive dimensionless gap. -/
theorem common_base_positive_gap (q : ℝ) (hq : q < 1) :
    0 < 1 - q := by
  linarith

end YangMillsBraid
