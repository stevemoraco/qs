import Mathlib

/-!
# AO ring-mode Doppler algebra firewall

This file formalizes only finite algebraic identities used in the Navier--Stokes
ring-mode research lane.

It does **not** formalize the Euler/Navier--Stokes PDE, the Albritton--Ożański
spectral theorem, Weber asymptotics, or any blow-up statement.

The certified cores are:

1. the AO coefficient `b` collapses after substituting
   `q = -Γ'/W'` and `Φ = 2 Γ Γ' / r^3`;
2. if the zero-phase stress is decomposed as
   `Rrθ = β r Rrz + E`, then the radial derivative of the leading
   helical-tangent channel cancels exactly from the Doppler combination;
3. the abstract sign pattern appearing in the Batchelor simultaneous
   critical-point equations forces a nonzero (indeed negative) Jacobian.
-/

namespace NSRingDopplerAlgebra

/-- Finite algebra behind the simplification

`b = β r² (1-βq) Φ / (q(1+β²r²))`

to

`b = -2 β Γ (W' + β Γ') / (r(1+β²r²))`.

All denominator hypotheses are stated explicitly. -/
theorem b_collapse
    {β r Γ Γp Wp q Φ : ℝ}
    (hr : r ≠ 0)
    (hΓp : Γp ≠ 0)
    (hWp : Wp ≠ 0)
    (hD : 1 + β^2 * r^2 ≠ 0)
    (hq : q = -Γp / Wp)
    (hΦ : Φ = 2 * Γ * Γp / r^3) :
    β * r^2 * (1 - β * q) * Φ / (q * (1 + β^2 * r^2)) =
      -2 * β * Γ * (Wp + β * Γp) / (r * (1 + β^2 * r^2)) := by
  rw [hq, hΦ]
  field_simp [hr, hΓp, hWp, hD]
  ring

/-- Same identity after writing `Γ = r V`.

This is the form used in the ring-polarization calculation:

`b = -2 β V H / (1+β²r²)`, where `H = W' + β(rV)'`. -/
theorem b_collapse_velocity_form
    {β r V Γp Wp q Φ : ℝ}
    (hr : r ≠ 0)
    (hΓp : Γp ≠ 0)
    (hWp : Wp ≠ 0)
    (hD : 1 + β^2 * r^2 ≠ 0)
    (hq : q = -Γp / Wp)
    (hΦ : Φ = 2 * (r * V) * Γp / r^3) :
    β * r^2 * (1 - β * q) * Φ / (q * (1 + β^2 * r^2)) =
      -2 * β * V * (Wp + β * Γp) / (1 + β^2 * r^2) := by
  rw [hq, hΦ]
  field_simp [hr, hΓp, hWp, hD]
  ring

/-- Exact cylindrical Reynolds-stress cancellation.

Think of

* `R` as `R_rz`,
* `Rp` as its radial derivative,
* `E = R_rθ - β r R_rz`,
* `Ep` as the radial derivative of `E`.

Then `R_rθ = β r R + E` and
`(R_rθ)' = β(R+rR')+E'`.

The Doppler forcing combination

`β (div R)_z - (div R)_θ / r`

contains no `R'` term after substitution. -/
theorem doppler_stress_cancellation
    {β r R Rp E Ep : ℝ}
    (hr : r ≠ 0) :
    β * (Rp + R / r) -
        (β * (R + r * Rp) + Ep + 2 * (β * r * R + E) / r) / r =
      -2 * β * R / r - Ep / r - 2 * E / r^2 := by
  field_simp [hr]
  ring

/-- In the exactly helical-tangent case `E=E'=0`, only the lower-order
cylindrical curvature term remains. -/
theorem exact_tangent_doppler_remainder
    {β r R Rp : ℝ}
    (hr : r ≠ 0) :
    β * (Rp + R / r) -
        (β * (R + r * Rp) + 2 * (β * r * R) / r) / r =
      -2 * β * R / r := by
  field_simp [hr]
  ring

/-- Abstract sign core of the Batchelor critical-point transversality.

At the AO simultaneous root the first critical equation has
`F1_r > 0`, `F1_β < 0`, while the second has
`F2_β = -2β` with `β>0` and `F2_r=g'(r)<0`.
The two-by-two Jacobian determinant is therefore strictly negative. -/
theorem critical_point_jacobian_negative
    {β F1r F1β gr : ℝ}
    (hβ : 0 < β)
    (hF1r : 0 < F1r)
    (hF1β : F1β < 0)
    (hgr : gr < 0) :
    F1r * (-2 * β) - F1β * gr < 0 := by
  have hprod : 0 < F1β * gr := mul_pos_of_neg_of_neg hF1β hgr
  nlinarith

/-- The corresponding derivative of the second critical equation along the
first-root branch is negative whenever the root moves to larger radius. -/
theorem critical_branch_crossing_negative
    {β gr rβ : ℝ}
    (hβ : 0 < β)
    (hgr : gr < 0)
    (hrβ : 0 < rβ) :
    gr * rβ - 2 * β < 0 := by
  have hprod : gr * rβ < 0 := mul_neg_of_neg_of_pos hgr hrβ
  linarith

/-- Scaling arithmetic used in the first nonzero defect channel:
`n^(-1/4)` amplitude followed by one `n^(3/4)` inner derivative gives
`n^(1/2)`. -/
theorem defect_derivative_exponent :
    (-(1 : ℚ) / 4) + (3 : ℚ) / 4 = (1 : ℚ) / 2 := by
  norm_num

/-- Two additional inner derivatives turn the `n^(1/2)` Doppler forcing
into an `n^2` curvature-scale contribution. -/
theorem doppler_curvature_exponent :
    (1 : ℚ) / 2 + 2 * ((3 : ℚ) / 4) = 2 := by
  norm_num

/-- At perturbative amplitude `A ~ S n^(-3/4)`, the regenerated Doppler
amplitude over a time `S^(-1)` carries exponent `n^(-1)`. -/
theorem regenerated_doppler_amplitude_exponent :
    2 * (-(3 : ℚ) / 4) + (1 : ℚ) / 2 = -1 := by
  norm_num

/-- Adding two inner derivatives to that regenerated Doppler amplitude
produces the `n^(1/2)` curvature amplification. -/
theorem regenerated_curvature_gain_exponent :
    (-1 : ℚ) + 2 * ((3 : ℚ) / 4) = (1 : ℚ) / 2 := by
  norm_num

#print axioms b_collapse
#print axioms b_collapse_velocity_form
#print axioms doppler_stress_cancellation
#print axioms exact_tangent_doppler_remainder
#print axioms critical_point_jacobian_negative
#print axioms critical_branch_crossing_negative
#print axioms defect_derivative_exponent
#print axioms doppler_curvature_exponent
#print axioms regenerated_doppler_amplitude_exponent
#print axioms regenerated_curvature_gain_exponent

end NSRingDopplerAlgebra
