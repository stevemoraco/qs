import Mathlib

/-!
# Shahmurov 2026 equation/type firewalls: finite algebra only

This file formalizes only elementary algebra and state-typing shadows behind a
hostile audit of arXiv:2604.09949v1. It does not formalize cylindrical vector
calculus, axisymmetric Navier--Stokes, the five-dimensional lift, streamfunction
recovery, the cited manuscript, or the Clay problem.
-/

namespace NSShahmurovEquationTypeFirewall

noncomputable def div3 (drUr ur r dzUz : ℝ) : ℝ :=
  drUr + ur / r + dzUz

noncomputable def div5 (drUr ur r dzUz : ℝ) : ℝ :=
  drUr + 3 * ur / r + dzUz

theorem both_divergence_laws_force_radial_zero
    {drUr ur r dzUz : ℝ}
    (hr : r ≠ 0)
    (h3 : div3 drUr ur r dzUz = 0)
    (h5 : div5 drUr ur r dzUz = 0) :
    ur = 0 := by
  unfold div3 div5 at h3 h5
  field_simp [hr] at h3 h5
  linarith

theorem five_divergence_gives_physical_defect
    {drUr ur r dzUz : ℝ}
    (hr : r ≠ 0)
    (h5 : div5 drUr ur r dzUz = 0) :
    div3 drUr ur r dzUz = -2 * ur / r := by
  unfold div3 div5 at *
  field_simp [hr] at h5 ⊢
  linarith

theorem nonzero_radial_blocks_three_divergence
    {drUr ur r dzUz : ℝ}
    (hr : r ≠ 0)
    (hur : ur ≠ 0)
    (h5 : div5 drUr ur r dzUz = 0) :
    div3 drUr ur r dzUz ≠ 0 := by
  intro h3
  exact hur (both_divergence_laws_force_radial_zero hr h3 h5)

structure LiftedState where
  F : ℝ
  G : ℝ

def swirlOnly (s : LiftedState) : ℝ := s.F

theorem swirl_projection_not_injective :
    ¬ Function.Injective swirlOnly := by
  intro hinj
  let s0 : LiftedState := ⟨0, 0⟩
  let s1 : LiftedState := ⟨0, 1⟩
  have hs : swirlOnly s0 = swirlOnly s1 := by
    rfl
  have heq : s0 = s1 := hinj hs
  have hG : s0.G = s1.G := congrArg LiftedState.G heq
  norm_num [s0, s1] at hG

theorem no_swirl_nonzero_vorticity_state :
    ∃ s : LiftedState, s.F = 0 ∧ s.G ≠ 0 := by
  exact ⟨⟨0, 1⟩, by norm_num, by norm_num⟩

theorem no_universal_vorticity_recovery_from_swirl :
    ¬ ∃ R : ℝ → ℝ, ∀ s : LiftedState, s.G = R s.F := by
  rintro ⟨R, hR⟩
  have h0 := hR (LiftedState.mk 0 0)
  have h1 := hR (LiftedState.mk 0 1)
  norm_num at h0 h1
  linarith

#print axioms both_divergence_laws_force_radial_zero
#print axioms five_divergence_gives_physical_defect
#print axioms nonzero_radial_blocks_three_divergence
#print axioms swirl_projection_not_injective
#print axioms no_swirl_nonzero_vorticity_state
#print axioms no_universal_vorticity_recovery_from_swirl

end NSShahmurovEquationTypeFirewall
