import Mathlib

/-!
# Hypocoercive synchronization gate for replicated packet amplitudes

This file formalizes only a finite two-mode linear algebra model: an amplified
replica defect is skew-coupled to a viscously damped auxiliary mode. It does not
formalize Fourier packets, Euler triads, Navier–Stokes evolution, invariant
manifolds, or singularity formation.
-/

namespace NSHypocoerciveSynchronization

/-- Amplified replica-defect component with skew transfer to a sink mode. -/
def defectRate (σ κ d z : ℝ) : ℝ := σ * d + κ * z

/-- Viscously damped sink component with the opposite skew transfer. -/
def sinkRate (μ κ d z : ℝ) : ℝ := -κ * d - μ * z

/-- Trace of the two-mode normal block. -/
def normalTrace (σ μ : ℝ) : ℝ := σ - μ

/-- Determinant of the two-mode normal block. -/
def normalDet (σ μ κ : ℝ) : ℝ := κ ^ 2 - σ * μ

/-- Characteristic polynomial of the two-mode normal block. -/
def charPoly (σ μ κ λ : ℝ) : ℝ :=
  λ ^ 2 + (μ - σ) * λ + (κ ^ 2 - σ * μ)

/-- BANKER: the skew coupling cancels exactly from the quadratic energy
balance; growth and viscosity are the only direct energy terms. -/
theorem skew_coupling_energy_identity (σ μ κ d z : ℝ) :
    d * defectRate σ κ d z + z * sinkRate μ κ d z =
      σ * d ^ 2 - μ * z ^ 2 := by
  unfold defectRate sinkRate
  ring

/-- The trace is negative exactly when sink damping exceeds defect growth. -/
theorem trace_negative_iff (σ μ : ℝ) :
    normalTrace σ μ < 0 ↔ σ < μ := by
  unfold normalTrace
  linarith

/-- The determinant is positive exactly past the product coupling threshold. -/
theorem determinant_positive_iff (σ μ κ : ℝ) :
    0 < normalDet σ μ κ ↔ σ * μ < κ ^ 2 := by
  unfold normalDet
  linarith

/-- Exact characteristic-polynomial expansion of the normal matrix. -/
theorem characteristic_polynomial_identity (σ μ κ λ : ℝ) :
    (λ - σ) * (λ + μ) + κ ^ 2 = charPoly σ μ κ λ := by
  unfold charPoly
  ring

/-- CRITIC: at the critical product threshold there is an explicit nonzero
zero mode, so strict determinant positivity cannot be weakened to equality. -/
theorem critical_threshold_has_nonzero_zero_mode
    {σ μ κ : ℝ}
    (hσ : σ ≠ 0)
    (hcrit : κ ^ 2 = σ * μ) :
    defectRate σ κ κ (-σ) = 0 ∧
      sinkRate μ κ κ (-σ) = 0 ∧
      (κ ≠ 0 ∨ -σ ≠ 0) := by
  constructor
  · unfold defectRate
    ring
  constructor
  · unfold sinkRate
    nlinarith [hcrit]
  · right
    exact neg_ne_zero.mpr hσ

/-- Below the product threshold the determinant is nonpositive. -/
theorem subthreshold_coupling_has_nonpositive_determinant
    {σ μ κ : ℝ}
    (hsub : κ ^ 2 ≤ σ * μ) :
    normalDet σ μ κ ≤ 0 := by
  unfold normalDet
  linarith

/-- The two scalar Hurwitz budgets unpack to the exact damping and coupling
inequalities. -/
theorem strict_normal_budget_unpacks
    {σ μ κ : ℝ}
    (htrace : normalTrace σ μ < 0)
    (hdet : 0 < normalDet σ μ κ) :
    σ < μ ∧ σ * μ < κ ^ 2 := by
  constructor
  · exact (trace_negative_iff σ μ).1 htrace
  · exact (determinant_positive_iff σ μ κ).1 hdet

/-- CLEANER: if the tangent amplifier is positive, the strict damping/product
budget forces the skew coupling square above the amplifier square. Thus the
coupling cannot be perturbative relative to the amplifier. -/
theorem strict_budget_forces_coupling_above_amplifier_square
    {σ μ κ : ℝ}
    (hσ : 0 < σ)
    (hμ : σ < μ)
    (hκ : σ * μ < κ ^ 2) :
    σ ^ 2 < κ ^ 2 := by
  calc
    σ ^ 2 = σ * σ := by ring
    _ < σ * μ := mul_lt_mul_of_pos_left hμ hσ
    _ < κ ^ 2 := hκ

/-- Increasing sink damping raises the product threshold when the amplifier is
nonnegative. -/
theorem stronger_sink_damping_raises_required_coupling_square
    {σ μ₁ μ₂ κ : ℝ}
    (hσ : 0 ≤ σ)
    (hμ : μ₁ ≤ μ₂)
    (hκ : σ * μ₂ < κ ^ 2) :
    σ * μ₁ < κ ^ 2 := by
  have hprod : σ * μ₁ ≤ σ * μ₂ := mul_le_mul_of_nonneg_left hμ hσ
  exact lt_of_le_of_lt hprod hκ

#print axioms skew_coupling_energy_identity
#print axioms trace_negative_iff
#print axioms determinant_positive_iff
#print axioms characteristic_polynomial_identity
#print axioms critical_threshold_has_nonzero_zero_mode
#print axioms subthreshold_coupling_has_nonpositive_determinant
#print axioms strict_normal_budget_unpacks
#print axioms strict_budget_forces_coupling_above_amplifier_square
#print axioms stronger_sink_damping_raises_required_coupling_square

end NSHypocoerciveSynchronization
