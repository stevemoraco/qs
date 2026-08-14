import Mathlib

namespace Millennium.YangMills

theorem limit_preserves_uniform_upper_bound
    (C : ℕ → ℝ) (L B : ℝ)
    (hbound : ∀ n, C n ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |C n - L| < ε) :
    L ≤ B := by
  by_contra h
  have hBL : B < L := lt_of_not_ge h
  let ε : ℝ := (L - B) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hconv ε hε with ⟨N, hN⟩
  have hclose := hN N le_rfl
  have hlower : -ε < C N - L := (abs_lt.mp hclose).1
  have hCN : C N ≤ B := hbound N
  dsimp [ε] at hlower
  linarith

theorem pointwise_limit_preserves_common_exponential_decay
    (C : ℕ → ℝ → ℝ) (Clim : ℝ → ℝ) (A m : ℝ)
    (hbound : ∀ n t, C n t ≤ A * Real.exp (-m * t))
    (hconv : ∀ t ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |C n t - Clim t| < ε) :
    ∀ t, Clim t ≤ A * Real.exp (-m * t) := by
  intro t
  exact limit_preserves_uniform_upper_bound
    (C := fun n => C n t)
    (L := Clim t)
    (B := A * Real.exp (-m * t))
    (fun n => hbound n t)
    (hconv t)

theorem pointwise_limit_preserves_variable_decay_with_uniform_floor
    (C : ℕ → ℝ → ℝ) (Clim : ℝ → ℝ)
    (A m0 : ℝ) (m : ℕ → ℝ)
    (hA : 0 ≤ A)
    (hm : ∀ n, m0 ≤ m n)
    (hbound : ∀ n t, 0 ≤ t → C n t ≤ A * Real.exp (-(m n) * t))
    (hconv : ∀ t ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, |C n t - Clim t| < ε) :
    ∀ t, 0 ≤ t → Clim t ≤ A * Real.exp (-m0 * t) := by
  intro t ht
  apply limit_preserves_uniform_upper_bound
    (C := fun n => C n t)
    (L := Clim t)
    (B := A * Real.exp (-m0 * t))
  · intro n
    calc
      C n t ≤ A * Real.exp (-(m n) * t) := hbound n t ht
      _ ≤ A * Real.exp (-m0 * t) := by
        apply mul_le_mul_of_nonneg_left _ hA
        apply Real.exp_le_exp.mpr
        nlinarith [hm n]
  · exact hconv t

theorem nearby_time_decay_from_monotone_grid
    (C : ℝ → ℝ) (A m s t δ : ℝ)
    (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hts : t ≤ s + δ)
    (hmono : C t ≤ C s)
    (hgrid : C s ≤ A * Real.exp (-m * s)) :
    C t ≤ A * Real.exp (m * δ - m * t) := by
  have hnonneg : 0 ≤ s + δ - t := by
    linarith
  have hprod : 0 ≤ m * (s + δ - t) := mul_nonneg hm hnonneg
  have hexp : Real.exp (-m * s) ≤ Real.exp (m * δ - m * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    C t ≤ C s := hmono
    _ ≤ A * Real.exp (-m * s) := hgrid
    _ ≤ A * Real.exp (m * δ - m * t) :=
      mul_le_mul_of_nonneg_left hexp hA

theorem positive_regulator_rates_need_not_have_uniform_floor :
    ∃ m : ℝ → ℝ,
      (∀ a, 0 < a → 0 < m a) ∧
      (∀ c, 0 < c → ∃ a, 0 < a ∧ m a < c) := by
  refine ⟨(fun a => a), ?_, ?_⟩
  · intro a ha
    simpa using ha
  · intro c hc
    refine ⟨c / 2, by linarith, ?_⟩
    dsimp
    linarith

#print axioms limit_preserves_uniform_upper_bound
#print axioms pointwise_limit_preserves_common_exponential_decay
#print axioms pointwise_limit_preserves_variable_decay_with_uniform_floor
#print axioms nearby_time_decay_from_monotone_grid
#print axioms positive_regulator_rates_need_not_have_uniform_floor

end Millennium.YangMills
