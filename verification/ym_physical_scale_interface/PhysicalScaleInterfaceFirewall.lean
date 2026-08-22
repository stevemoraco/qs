import Mathlib

/-!
# Yang--Mills physical-scale interface firewall

If `gamma` is a dimensionless lattice decay exponent, `a` is the lattice
spacing, and `Lambda` is a positive transmutation scale, then the physical gap
ratio is `gamma / (a * Lambda)`. The finite arithmetic below shows that
pointwise positivity of `gamma` gives neither the required lower margin nor a
finite upper window, while a regulator-independent positive lattice-step lower
bound can force overshoot when `a * Lambda` becomes small.

This is scalar real arithmetic only. It does not identify a Gibbs Poincare/LSI
constant with a physical Hamiltonian gap, construct an OS limit, or prove the
Clay Yang--Mills theorem.
-/

namespace Millennium.YangMills.PhysicalScaleInterfaceFirewall

noncomputable def physicalGap (gamma a : ℝ) : ℝ := gamma / a

noncomputable def normalizedPhysicalGap (gamma a Lambda : ℝ) : ℝ :=
  physicalGap gamma a / Lambda

theorem normalizedPhysicalGap_eq (gamma a Lambda : ℝ) :
    normalizedPhysicalGap gamma a Lambda = gamma / (a * Lambda) := by
  simp [normalizedPhysicalGap, physicalGap, div_div]

theorem lattice_decay_exponent_to_physical_time
    {gamma a n : ℝ} (ha : a ≠ 0) :
    -(gamma / a) * (a * n) = -gamma * n := by
  field_simp

theorem normalized_window_of_lattice_window
    {gamma a Lambda c C : ℝ}
    (ha : 0 < a) (hLambda : 0 < Lambda)
    (hlower : c * (a * Lambda) ≤ gamma)
    (hupper : gamma ≤ C * (a * Lambda)) :
    c ≤ normalizedPhysicalGap gamma a Lambda ∧
      normalizedPhysicalGap gamma a Lambda ≤ C := by
  rw [normalizedPhysicalGap_eq]
  have hscale : 0 < a * Lambda := mul_pos ha hLambda
  constructor
  · exact (le_div_iff₀ hscale).2 hlower
  · exact (div_le_iff₀ hscale).2 hupper

theorem fixed_lattice_lower_bound_forces_overshoot
    {gamma gamma0 a Lambda C : ℝ}
    (hscale : 0 < a * Lambda)
    (hgamma : gamma0 ≤ gamma)
    (hsmall : C * (a * Lambda) < gamma0) :
    C < normalizedPhysicalGap gamma a Lambda := by
  rw [normalizedPhysicalGap_eq]
  exact (lt_div_iff₀ hscale).2 (lt_of_lt_of_le hsmall hgamma)

theorem positive_lattice_exponent_can_undershoot
    {a Lambda c : ℝ}
    (ha : 0 < a) (hLambda : 0 < Lambda) (hc : 0 < c) :
    ∃ gamma : ℝ, 0 < gamma ∧ normalizedPhysicalGap gamma a Lambda < c := by
  have hscale : 0 < a * Lambda := mul_pos ha hLambda
  refine ⟨(c / 2) * (a * Lambda), ?_, ?_⟩
  · exact mul_pos (by linarith) hscale
  · rw [normalizedPhysicalGap_eq]
    have hne : a * Lambda ≠ 0 := ne_of_gt hscale
    calc
      ((c / 2) * (a * Lambda)) / (a * Lambda) = c / 2 := by
        exact mul_div_cancel_right₀ (c / 2) hne
      _ < c := by linarith

theorem positive_lattice_exponent_can_overshoot
    {a Lambda C : ℝ}
    (ha : 0 < a) (hLambda : 0 < Lambda) (hC : 0 ≤ C) :
    ∃ gamma : ℝ, 0 < gamma ∧ C < normalizedPhysicalGap gamma a Lambda := by
  have hscale : 0 < a * Lambda := mul_pos ha hLambda
  refine ⟨(C + 1) * (a * Lambda), ?_, ?_⟩
  · exact mul_pos (by linarith) hscale
  · rw [normalizedPhysicalGap_eq]
    have hne : a * Lambda ≠ 0 := ne_of_gt hscale
    calc
      C < C + 1 := by linarith
      _ = ((C + 1) * (a * Lambda)) / (a * Lambda) := by
        symm
        exact mul_div_cancel_right₀ (C + 1) hne

theorem positive_static_constant_does_not_supply_scale_bridge
    {rho a Lambda c : ℝ}
    (hrho : 0 < rho) (ha : 0 < a) (hLambda : 0 < Lambda) (hc : 0 < c) :
    ∃ gamma : ℝ,
      0 < rho ∧ 0 < gamma ∧ normalizedPhysicalGap gamma a Lambda < c := by
  rcases positive_lattice_exponent_can_undershoot ha hLambda hc with
    ⟨gamma, hgamma, hsmall⟩
  exact ⟨gamma, hrho, hgamma, hsmall⟩

#print axioms physicalGap
#print axioms normalizedPhysicalGap
#print axioms normalizedPhysicalGap_eq
#print axioms lattice_decay_exponent_to_physical_time
#print axioms normalized_window_of_lattice_window
#print axioms fixed_lattice_lower_bound_forces_overshoot
#print axioms positive_lattice_exponent_can_undershoot
#print axioms positive_lattice_exponent_can_overshoot
#print axioms positive_static_constant_does_not_supply_scale_bridge

end Millennium.YangMills.PhysicalScaleInterfaceFirewall
