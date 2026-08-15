import Mathlib

/-!
# Yu reservoir reverse-coercivity firewall

Finite real algebra only.

These theorems isolate a logical issue in reverse-using an absorption estimate
of the schematic form

  A ≤ η P + C O.

A positive defect `A` does not by itself force a positive diffusion payment `P`:
the lower-order reservoir `O` can pay the entire bound.  A genuine reverse
coercivity statement needs an additional reservoir-gap hypothesis.

No theorem below formalizes Yu's filtered-vorticity estimates, Navier--Stokes,
or any Millennium Prize statement.
-/

namespace NSYuReservoirGapFirewall

theorem positive_defect_zero_diffusion_countermodel :
    let A : ℝ := 1
    let P : ℝ := 0
    let O : ℝ := 1
    let η : ℝ := 1
    let C : ℝ := 1
    0 < A ∧ 0 ≤ P ∧ 0 < O ∧
      A ≤ η * P + C * O ∧ ¬ (0 < P) := by
  norm_num

theorem upper_absorption_does_not_force_positive_diffusion :
    ¬ (∀ A P O η C : ℝ,
        0 < A → 0 < η → 0 < C → 0 ≤ P → 0 ≤ O →
        A ≤ η * P + C * O → 0 < P) := by
  intro h
  have hp := h 1 0 1 1 1
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hp

theorem reservoir_ratio_gap_reverse_coercivity
    {A P O η C Λ : ℝ}
    (hΛ : 0 ≤ Λ)
    (hC : 0 ≤ C)
    (hupper : A ≤ η * P + C * O)
    (hgap : Λ * O ≤ A) :
    (Λ - C) * A ≤ η * Λ * P := by
  have h1 : Λ * A ≤ Λ * (η * P + C * O) :=
    mul_le_mul_of_nonneg_left hupper hΛ
  have h2 : C * (Λ * O) ≤ C * A :=
    mul_le_mul_of_nonneg_left hgap hC
  nlinarith

theorem relative_reservoir_fraction_reverse_coercivity
    {A P η θ : ℝ}
    (hupper : A ≤ η * P + θ * A) :
    (1 - θ) * A ≤ η * P := by
  linarith

theorem strict_relative_reservoir_forces_positive_diffusion
    {A P η θ : ℝ}
    (hA : 0 < A)
    (hη : 0 < η)
    (hθ : θ < 1)
    (hupper : A ≤ η * P + θ * A) :
    0 < P := by
  have hcore : (1 - θ) * A ≤ η * P :=
    relative_reservoir_fraction_reverse_coercivity hupper
  have hleft : 0 < (1 - θ) * A :=
    mul_pos (sub_pos.mpr hθ) hA
  have hηP : 0 < η * P := lt_of_lt_of_le hleft hcore
  nlinarith

theorem admissible_filter_ratio_factor_ge_sixty_four
    {σ ρ : ℝ}
    (hσ : 0 < σ)
    (hσρ : σ ≤ ρ)
    (hρ : ρ ≤ (1 : ℝ) / 4) :
    64 ≤ ρ ^ 2 / σ ^ 5 := by
  have hρpos : 0 < ρ := lt_of_lt_of_le hσ hσρ
  have hσ5 : σ ^ 5 ≤ ρ ^ 5 := by
    gcongr
  have hρ3 : ρ ^ 3 ≤ ((1 : ℝ) / 4) ^ 3 := by
    gcongr
  have hρ3' : 64 * ρ ^ 3 ≤ 1 := by
    norm_num at hρ3 ⊢
    nlinarith
  have h64 : 64 * σ ^ 5 ≤ ρ ^ 2 := by
    calc
      64 * σ ^ 5 ≤ 64 * ρ ^ 5 := by nlinarith
      _ = 64 * ρ ^ 2 * ρ ^ 3 := by ring
      _ ≤ ρ ^ 2 := by
        have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
        nlinarith
  have hσ5pos : 0 < σ ^ 5 := pow_pos hσ 5
  exact (le_div_iff₀ hσ5pos).2 h64

theorem no_uniform_positive_reservoir_gap_from_positivity
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ A O : ℝ, 0 < A ∧ 0 < O ∧ A < Λ * O := by
  refine ⟨Λ / 2, 1, ?_, by norm_num, ?_⟩
  · linarith
  · norm_num
    linarith

#print axioms positive_defect_zero_diffusion_countermodel
#print axioms upper_absorption_does_not_force_positive_diffusion
#print axioms reservoir_ratio_gap_reverse_coercivity
#print axioms relative_reservoir_fraction_reverse_coercivity
#print axioms strict_relative_reservoir_forces_positive_diffusion
#print axioms admissible_filter_ratio_factor_ge_sixty_four
#print axioms no_uniform_positive_reservoir_gap_from_positivity

end NSYuReservoirGapFirewall
