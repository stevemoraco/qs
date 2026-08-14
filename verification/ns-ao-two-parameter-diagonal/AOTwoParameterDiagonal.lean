import Mathlib

/-!
# AO two-parameter Navier--Stokes diagonal

Finite scaling algebra only.  This file certifies that the corrected
Albritton--Ożański packet bookkeeping has a nonempty asymptotic diagonal after
separating the physical base scale from the high ring-mode index.

It does NOT prove viscous spectral persistence, nonlinear instability,
regeneration, blow-up, or the Clay Navier--Stokes statement.
-/

namespace Millennium.NavierStokes.AOTwoParameterDiagonal

/-- Exact polynomial diagonal:

* physical base scale `N = M^24`;
* AO mode index `k = M^2`;
* e-fold budget `L = M`;
* `N^(1/3)` is represented exactly by `M^8`.

The leading relative viscous factor `k^2/N^(1/3)` is exactly `M^-4`. -/
theorem relative_viscosity_diagonal (M : ℚ) (hM : M ≠ 0) :
    (M^2)^2 / M^8 = 1 / M^4 := by
  field_simp [hM]

/-- The conservative accumulated perturbation budget
`L^2 k^2 / N^(1/3)` is exactly `M^-2` on the same diagonal. -/
theorem accumulated_budget_diagonal (M : ℚ) (hM : M ≠ 0) :
    M^2 * (M^2)^2 / M^8 = 1 / M^2 := by
  field_simp [hM]

/-- The axial-window modulation ratio for `B_z=N^(2/3)` versus the physical
carrier `N*k` becomes `M^-10`: `M^16/(M^24*M^2)`. -/
theorem axial_window_ratio_diagonal (M : ℚ) (hM : M ≠ 0) :
    M^16 / (M^24 * M^2) = 1 / M^10 := by
  field_simp [hM]

/-- For `M>1`, the corrected leading viscous factor is strictly below one. -/
theorem relative_viscosity_lt_one
    (M : ℚ) (hM : 1 < M) :
    1 / M^4 < 1 := by
  have hM0 : 0 < M := lt_trans (by norm_num) hM
  have hpow : 1 < M^4 := by nlinarith [sq_nonneg (M^2 - 1)]
  exact (div_lt_one (by positivity)).2 hpow

/-- For `M>1`, the accumulated perturbation factor is strictly below one. -/
theorem accumulated_budget_lt_one
    (M : ℚ) (hM : 1 < M) :
    1 / M^2 < 1 := by
  have hpow : 1 < M^2 := by nlinarith
  exact (div_lt_one (by positivity)).2 hpow

/-- Both independent parameters genuinely diverge along integer master scales:
for every requested threshold there is an integer `M` whose mode index `M^2`
and e-fold budget `M` exceed it. -/
theorem cofinal_mode_and_efold_budget (K : ℕ) :
    ∃ M : ℕ, K < M ∧ K < M^2 := by
  refine ⟨K + 2, by omega, ?_⟩
  nlinarith

#print axioms relative_viscosity_diagonal
#print axioms accumulated_budget_diagonal
#print axioms axial_window_ratio_diagonal
#print axioms relative_viscosity_lt_one
#print axioms accumulated_budget_lt_one
#print axioms cofinal_mode_and_efold_budget

end Millennium.NavierStokes.AOTwoParameterDiagonal
