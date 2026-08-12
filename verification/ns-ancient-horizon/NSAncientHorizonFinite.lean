import Mathlib

/-!
# Navier--Stokes ancient-profile horizon: finite scalar ledger

This file formalizes only scalar identities and implications used after the
analytic local-lifespan and scaling theorems are supplied.

It does not formalize Navier--Stokes solutions, Sobolev inequalities, `L^6`
local well-posedness, pressure reconstruction, ancient mild solutions,
compactness, singularities, or the Clay statement.
-/

namespace MillenniumBraid
namespace NSAncientHorizonFinite

/-- The velocity-normalized ratio/horizon product is exactly the physical
squared-enstrophy blow-up product when `D = U * R`. -/
theorem normalized_horizon_enstrophy_identity
    (remaining U R : ℝ) :
    (remaining * U ^ 2) * R ^ 2 =
      remaining * (U * R) ^ 2 := by
  ring

/-- A supplied local-lifespan lower budget transfers through a supplied powered
Sobolev estimate to the ratio/horizon floor. -/
theorem lifespan_floor_transfer
    (c τ L4 ratioBound : ℝ)
    (hτ : 0 ≤ τ)
    (hlife : c ≤ τ * L4)
    (hSobolevPower : L4 ≤ ratioBound) :
    c ≤ τ * ratioBound := by
  exact hlife.trans (mul_le_mul_of_nonneg_left hSobolevPower hτ)

/-- If the normalized ratio is at most `M`, an inverse-square horizon floor
implies one common positive normalized future interval. -/
theorem bounded_ratio_gives_horizon_floor
    (c τ R M : ℝ)
    (hc : 0 < c)
    (hR : 0 ≤ R)
    (hRM : R ≤ M)
    (hbudget : c ≤ τ * R ^ 2) :
    c ≤ τ * M ^ 2 := by
  have hM : 0 ≤ M := le_trans hR hRM
  have hsq : R ^ 2 ≤ M ^ 2 := by nlinarith
  have hτ : 0 ≤ τ := by
    by_contra hneg
    have hτneg : τ < 0 := lt_of_not_ge hneg
    have : τ * R ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hτneg) (sq_nonneg R)
    linarith
  exact hbudget.trans (mul_le_mul_of_nonneg_left hsq hτ)

/-- Exact scalar shadow of the future-dissipation scaling:
`(D/U) * (U^2 dt) = U * (D dt)` when `U` is nonzero. -/
theorem future_dissipation_scaling_identity
    (D U dt : ℝ) (hU : U ≠ 0) :
    (D / U) * (U ^ 2 * dt) = U * (D * dt) := by
  field_simp
  ring

/-- Integrability of a tail and growth of an amplitude do not by themselves
force their product to vanish: this exact family is constantly one. -/
theorem vanishing_tail_times_growing_amplitude
    (n : ℕ) :
    ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by
  have h : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- A finite normalized horizon and an infinite-horizon escape are logically
separate branches. -/
theorem finite_or_large_horizon
    (τ B : ℝ) :
    τ ≤ B ∨ B < τ := by
  exact le_or_gt τ B

#print axioms normalized_horizon_enstrophy_identity
#print axioms lifespan_floor_transfer
#print axioms bounded_ratio_gives_horizon_floor
#print axioms future_dissipation_scaling_identity
#print axioms vanishing_tail_times_growing_amplitude
#print axioms finite_or_large_horizon

end NSAncientHorizonFinite
end MillenniumBraid
