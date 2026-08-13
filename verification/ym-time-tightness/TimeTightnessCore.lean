import Mathlib

namespace TimeTightnessCore

def r (n : ℕ) : ℚ := 1 / ((n : ℚ) + 2)
def C (n k : ℕ) : ℚ := (r n) ^ k
def V (n : ℕ) : ℚ := C n 0

theorem V_one (n : ℕ) : V n = 1 := by
  simp [V, C]

theorem r_pos (n : ℕ) : 0 < r n := by
  unfold r
  positivity

theorem C_pos (n k : ℕ) : 0 < C n k := by
  unfold C
  exact pow_pos (r_pos n) k

theorem r_le_half (n : ℕ) : r n ≤ (1 : ℚ) / 2 := by
  unfold r
  have hd : 0 < (n : ℚ) + 2 := by positivity
  have hn : (0 : ℚ) ≤ n := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith

theorem C_succ (n k : ℕ) : C n (k + 1) = C n k * r n := by
  simp [C, pow_succ]

theorem geometric_bound (n k : ℕ) : C n k ≤ ((1 : ℚ) / 2) ^ k := by
  induction k with
  | zero => simp [C]
  | succ k ih =>
      rw [C_succ, pow_succ]
      exact mul_le_mul ih (r_le_half n) (le_of_lt (r_pos n)) (by positivity)

theorem one_step_small {ε : ℚ} (hε : 0 < ε) : ∃ n : ℕ, C n 1 < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε : ℚ)
  refine ⟨N, ?_⟩
  have hNq : (1 / ε : ℚ) < (N : ℚ) + 2 := by
    have hN2 : (N : ℚ) < (N : ℚ) + 2 := by norm_num
    exact lt_trans hN hN2
  have hmul : 1 < ε * ((N : ℚ) + 2) := by
    have h := (div_lt_iff₀ hε).1 hNq
    simpa [mul_comm] using h
  have hd : 0 < (N : ℚ) + 2 := by positivity
  have hdiv : 1 / ((N : ℚ) + 2) < ε := (div_lt_iff₀ hd).2 hmul
  simpa [C, r] using hdiv

theorem defect_ge_half (n : ℕ) : (1 : ℚ) / 2 ≤ V n - C n 1 := by
  have hcov : C n 1 ≤ (1 : ℚ) / 2 := by
    simpa [C] using r_le_half n
  rw [V_one]
  linarith

theorem no_vanishing_defect :
    ¬ (∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → V n - C n 1 < ε) := by
  intro h
  rcases h (1 / 4 : ℚ) (by norm_num) with ⟨N, hN⟩
  have hupper := hN N le_rfl
  have hlower := defect_ge_half N
  norm_num at hupper hlower
  linarith

theorem countermodel :
    ∃ F : ℕ → ℕ → ℚ,
      (∀ n, F n 0 = 1) ∧
      (∀ n k, 0 < F n k) ∧
      (∀ n k, F n k ≤ ((1 : ℚ) / 2) ^ k) ∧
      (∀ ε : ℚ, 0 < ε → ∃ n, F n 1 < ε) := by
  refine ⟨C, ?_, C_pos, geometric_bound, ?_⟩
  · intro n
    simpa [V] using V_one n
  · intro ε hε
    exact one_step_small hε

#print axioms V_one
#print axioms r_pos
#print axioms C_pos
#print axioms r_le_half
#print axioms C_succ
#print axioms geometric_bound
#print axioms one_step_small
#print axioms defect_ge_half
#print axioms no_vanishing_defect
#print axioms countermodel

end TimeTightnessCore
