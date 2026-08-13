import Mathlib

/-!
# Finite accumulating-force firewall algebra

This file formalizes the scalar inequalities used in the smooth-force relay
obstruction.  It does not formalize bump-function derivative scaling or the
Navier--Stokes PDE.
-/

namespace Millennium.NavierStokes

/-- A pulse of amplitude `A` lasting `τ` cannot produce an increment larger
than `A τ` under the normalized scalar forcing model. -/
theorem transfer_forces_amplitude
    (A τ d : ℝ)
    (hA : 0 ≤ A) (hτ : 0 < τ) (hd : 0 ≤ d)
    (htransfer : d ≤ A * τ) :
    d / τ ≤ A := by
  exact (div_le_iff₀ hτ).2 htransfer

/-- If pulse amplitudes tend to zero while they must be at least `d/τ`, then
`d/τ` also tends to zero. -/
theorem transfer_ratio_le_amplitude
    (A τ d : ℕ → ℝ)
    (hτ : ∀ k, 0 < τ k)
    (htransfer : ∀ k, d k / τ k ≤ A k)
    (hzero : Filter.Tendsto A Filter.atTop (nhds 0))
    (hnonneg : ∀ k, 0 ≤ d k / τ k) :
    Filter.Tendsto (fun k => d k / τ k) Filter.atTop (nhds 0) := by
  apply squeeze_zero' hnonneg htransfer hzero

/-- A transfer bounded below by a positive constant is incompatible with a
vanishing amplitude-duration ratio. -/
theorem positive_transfer_not_ratio_zero
    (τ d : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hτzero : Filter.Tendsto τ Filter.atTop (nhds 0))
    (hτpos : ∀ k, 0 < τ k)
    (hd : ∀ k, c ≤ d k) :
    ¬ Filter.Tendsto (fun k => d k / τ k) Filter.atTop (nhds 0) := by
  intro hratio
  have hτinv : Filter.Tendsto (fun k => c / τ k) Filter.atTop Filter.atTop := by
    exact tendsto_const_div_atTop_of_pos hc hτzero
  have hle : ∀ k, c / τ k ≤ d k / τ k := by
    intro k
    exact (div_le_div_iff_of_pos_right (hτpos k)).2 (hd k)
  have hdivTop : Filter.Tendsto (fun k => d k / τ k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' hle hτinv
  exact not_tendsto_nhds_of_tendsto_atTop hdivTop hratio

end Millennium.NavierStokes
