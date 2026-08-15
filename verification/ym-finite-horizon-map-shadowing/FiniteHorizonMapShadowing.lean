import Mathlib

namespace Millennium.YangMills

def shadowBudget (K : ℝ) (eps : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => K * shadowBudget K eps n + eps n

@[simp] theorem shadowBudget_zero (K : ℝ) (eps : ℕ → ℝ) :
    shadowBudget K eps 0 = 0 := rfl

@[simp] theorem shadowBudget_succ (K : ℝ) (eps : ℕ → ℝ) (n : ℕ) :
    shadowBudget K eps (n + 1) = K * shadowBudget K eps n + eps n := rfl

theorem finite_horizon_shadowing
    (err eps : ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (herr0 : err 0 ≤ 0)
    (hstep : ∀ n, err (n + 1) ≤ K * err n + eps n) :
    ∀ N, err N ≤ shadowBudget K eps N := by
  intro N
  induction N with
  | zero =>
      simpa using herr0
  | succ n ih =>
      calc
        err (n + 1) ≤ K * err n + eps n := hstep n
        _ ≤ K * shadowBudget K eps n + eps n := by
          have hmul : K * err n ≤ K * shadowBudget K eps n :=
            mul_le_mul_of_nonneg_left ih hK
          linarith
        _ = shadowBudget K eps (n + 1) := by
          rfl

theorem finite_horizon_orbit_error
    (err localErr : ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hstart : err 0 = 0)
    (hstep : ∀ n, err (n + 1) ≤ K * err n + localErr n) :
    ∀ N, err N ≤ shadowBudget K localErr N := by
  apply finite_horizon_shadowing err localErr hK
  · simp [hstart]
  · exact hstep

#print axioms finite_horizon_shadowing
#print axioms finite_horizon_orbit_error

end Millennium.YangMills
