import Mathlib

/-!
# Yang--Mills physical-scale interface firewall

This file isolates the dimensional conversion that any lattice/functional-inequality
mass-gap argument must cross before it can imply a four-dimensional continuum
Hamiltonian gap at the Yang--Mills transmutation scale.

If `gamma` is a dimensionless lattice decay exponent and `a` is the lattice
spacing, then the corresponding physical inverse correlation length is
`gamma / a`. Relative to a positive transmutation scale `Lambda`, the relevant
quantity is therefore

  `gamma / (a * Lambda)`.

A positive (even regulator-uniform) lower bound on `gamma` is not automatically
the desired continuum statement. When `a * Lambda` is small, such a bound can
instead force this normalized physical ratio to be arbitrarily large. Under a
compatible nontrivial OS semigroup limit, the separate overshoot theorem then
shows why this is a warning rather than a solution: all centered finite-energy
spectral weight may escape.

Conversely, pointwise positivity of `gamma` alone can sit arbitrarily far below
any prescribed positive normalized physical margin.

The correct finite arithmetic target is a two-sided scale window

  `c * (a * Lambda) <= gamma <= C * (a * Lambda)`.

This is scalar real arithmetic only. It does not identify a Gibbs Poincare/LSI
constant with a transfer-matrix decay exponent, does not prove Euclidean
clustering, does not construct an Osterwalder--Schrader limit, and does not
prove the Clay Yang--Mills theorem.
-/

namespace Millennium.YangMills.PhysicalScaleInterfaceFirewall

/-- Physical inverse correlation length associated to a lattice-step exponent. -/
def physicalGap (gamma a : ℝ) : ℝ := gamma / a

/-- Physical gap normalized by the dimensional-transmutation scale. -/
def normalizedPhysicalGap (gamma a Lambda : ℝ) : ℝ :=
  physicalGap gamma a / Lambda

/-- The dimensionless lattice exponent converts exactly to `gamma / (a*Lambda)`
when measured in units of the transmutation scale. -/
theorem normalizedPhysicalGap_eq
    (gamma a Lambda : ℝ) :
    normalizedPhysicalGap gamma a Lambda = gamma / (a * Lambda) := by
  simp [normalizedPhysicalGap, physicalGap, div_div]

/-- Rewriting a lattice decay exponent in physical time `t = a*n` divides its
rate by `a`. This is the scalar exponent identity behind the conversion. -/
theorem lattice_decay_exponent_to_physical_time
    {gamma a n : ℝ} (ha : a ≠ 0) :
    -(gamma / a) * (a * n) = -gamma * n := by
  field_simp
  ring

/-- A two-sided lattice-scale window is exactly a two-sided physical gap window
in units of `Lambda`. -/
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

/-- A regulator-independent positive lattice-step exponent becomes *too large*
in physical transmutation units once `a*Lambda` is sufficiently small.
This is the finite inequality behind the overshoot warning. -/
theorem fixed_lattice_lower_bound_forces_overshoot
    {gamma gamma0 a Lambda C : ℝ}
    (hscale : 0 < a * Lambda)
    (hgamma : gamma0 ≤ gamma)
    (hsmall : C * (a * Lambda) < gamma0) :
    C < normalizedPhysicalGap gamma a Lambda := by
  rw [normalizedPhysicalGap_eq]
  exact (lt_div_iff₀ hscale).2 (lt_of_lt_of_le hsmall hgamma)

/-- Pointwise positivity of a lattice exponent supplies no prescribed positive
normalized physical margin. For every requested `c>0`, there is a positive
exponent whose normalized ratio is exactly `c/2`. -/
theorem positive_lattice_exponent_can_undershoot
    {a Lambda c : ℝ}
    (ha : 0 < a) (hLambda : 0 < Lambda) (hc : 0 < c) :
    ∃ gamma : ℝ,
      0 < gamma ∧ normalizedPhysicalGap gamma a Lambda < c := by
  have hscale : 0 < a * Lambda := mul_pos ha hLambda
  refine ⟨(c / 2) * (a * Lambda), ?_, ?_⟩
  · exact mul_pos (by linarith) hscale
  · rw [normalizedPhysicalGap_eq]
    have hne : a * Lambda ≠ 0 := ne_of_gt hscale
    calc
      ((c / 2) * (a * Lambda)) / (a * Lambda) = c / 2 := by
        exact mul_div_cancel_right₀ (c / 2) hne
      _ < c := by linarith

/-- Positivity also supplies no finite normalized upper window: for every
nonnegative requested ceiling `C`, a positive exponent can exceed it by one
full unit in transmutation-normalized physical scale. -/
theorem positive_lattice_exponent_can_overshoot
    {a Lambda C : ℝ}
    (ha : 0 < a) (hLambda : 0 < Lambda) (hC : 0 ≤ C) :
    ∃ gamma : ℝ,
      0 < gamma ∧ C < normalizedPhysicalGap gamma a Lambda := by
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

/-- A positive static functional-inequality constant can coexist with an
arbitrarily small normalized physical decay exponent unless a theorem relates
that constant quantitatively to the decay exponent at the correct scale. -/
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
