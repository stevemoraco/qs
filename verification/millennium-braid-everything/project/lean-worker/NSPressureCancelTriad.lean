import Mathlib

namespace NSPressureCancelTriad

/-- Equal-shell identity for the carriers `k₁=(K,n,0)` and `k₂=(-K,n,0)`. -/
theorem equal_high_shell (K n : ℝ) :
    K ^ 2 + n ^ 2 = (-K) ^ 2 + n ^ 2 := by
  ring

/-- `a=(n,-K,K)` is transverse to `k₁=(K,n,0)`. -/
theorem a_transverse_k1 (K n : ℝ) :
    n * K + (-K) * n = 0 := by
  ring

/-- `b=(n,K,-K)` is transverse to `k₂=(-K,n,0)`. -/
theorem b_transverse_k2 (K n : ℝ) :
    n * (-K) + K * n = 0 := by
  ring

/-- Cross dot products have equal magnitude and opposite sign. -/
theorem cross_dot_a_k2 (K n : ℝ) :
    n * (-K) + (-K) * n = -2 * K * n := by
  ring

theorem cross_dot_b_k1 (K n : ℝ) :
    n * K + K * n = 2 * K * n := by
  ring

/-- For the difference channel, the unnormalized cross-interaction numerator
has zero `y` component. -/
theorem difference_channel_y_zero (K n : ℝ) :
    (2 * K * n) * (-K) - (-2 * K * n) * K = 0 := by
  ring

/-- For the difference channel, the unnormalized cross-interaction numerator
has zero `z` component. -/
theorem difference_channel_z_zero (K n : ℝ) :
    (2 * K * n) * K - (-2 * K * n) * (-K) = 0 := by
  ring

/-- The remaining difference-channel component is parallel to
`k₁-k₂=(2K,0,0)`: its `x` numerator is `4 K n²`. -/
theorem difference_channel_x (K n : ℝ) :
    (2 * K * n) * n - (-2 * K * n) * n = 4 * K * n ^ 2 := by
  ring

/-- In the sum channel, the transverse `z` numerator is exactly `4 K² n`.
After dividing by the common polarization norm squared `n²+2K²`, this is
the visible Leray coefficient recorded in the human proof. -/
theorem sum_channel_z (K n : ℝ) :
    (2 * K * n) * K + (-2 * K * n) * (-K) = 4 * K ^ 2 * n := by
  ring

/-- The normalized visible low-channel coefficient is positive when both
carrier parameters are positive. -/
theorem low_coefficient_pos {K n : ℝ} (hK : 0 < K) (hn : 0 < n) :
    0 < 4 * K ^ 2 * n / (n ^ 2 + 2 * K ^ 2) := by
  have hden : 0 < n ^ 2 + 2 * K ^ 2 := by positivity
  positivity

/-- The coefficient is strictly below `2n`; this quantifies its approach to
the low-shell scale without importing any asymptotic theorem. -/
theorem low_coefficient_lt_two_n {K n : ℝ} (hK : 0 < K) (hn : 0 < n) :
    4 * K ^ 2 * n / (n ^ 2 + 2 * K ^ 2) < 2 * n := by
  have hden : 0 < n ^ 2 + 2 * K ^ 2 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith [sq_pos_of_pos hn]

#print axioms equal_high_shell
#print axioms a_transverse_k1
#print axioms b_transverse_k2
#print axioms cross_dot_a_k2
#print axioms cross_dot_b_k1
#print axioms difference_channel_y_zero
#print axioms difference_channel_z_zero
#print axioms difference_channel_x
#print axioms sum_channel_z
#print axioms low_coefficient_pos
#print axioms low_coefficient_lt_two_n

end NSPressureCancelTriad
