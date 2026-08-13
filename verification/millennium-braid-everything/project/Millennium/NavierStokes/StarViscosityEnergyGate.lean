import Mathlib

/-!
# Finite star-rotor energy/speed firewall

This file formalizes the real algebra behind the estimate
`G ≤ C N sqrt(E_R)` and the resulting energy lower bound needed to transfer
on a viscous time scale.  It does not formalize Fourier symbols, heat flow,
or Navier--Stokes.
-/

namespace Millennium.NavierStokes

/-- If every arm coefficient is bounded by `C N`, then aggregate squared
coupling is bounded by `C^2 N^2` times relay energy. -/
theorem aggregateCoupling_sq_le
    {ι : Type*} [Fintype ι]
    (Γ r : ι → ℝ) (C N : ℝ)
    (hCN : 0 ≤ C * N)
    (hΓ : ∀ j, |Γ j| ≤ C * N) :
    ∑ j, (Γ j * r j) ^ 2
      ≤ (C * N) ^ 2 * ∑ j, (r j) ^ 2 := by
  calc
    ∑ j, (Γ j * r j) ^ 2
        ≤ ∑ j, ((C * N) * r j) ^ 2 := by
          gcongr with j
          rw [mul_pow, mul_pow]
          gcongr
          exact sq_le_sq₀ (abs_nonneg _) hCN (hΓ j)
    _ = (C * N) ^ 2 * ∑ j, (r j) ^ 2 := by
          simp_rw [mul_pow]
          rw [← mul_sum]

/-- A transfer completed by time `η/N^2` under speed ceiling
`G ≤ C N sqrt(E)` requires `E ≥ N^2/(4 C^2 η^2)` up to the normalized
quarter-period constant `1/2`. -/
theorem viscousTime_forces_energy
    (G C N E η : ℝ)
    (hG : 0 < G) (hC : 0 < C) (hN : 0 < N)
    (hE : 0 ≤ E) (hη : 0 < η)
    (hspeed : G ^ 2 ≤ C ^ 2 * N ^ 2 * E)
    (htime : 1 / (2 * G) ≤ η / N ^ 2) :
    N ^ 2 / (4 * C ^ 2 * η ^ 2) ≤ E := by
  have h2G : 0 < 2 * G := by positivity
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  have htime' : N ^ 2 ≤ 2 * G * η := by
    apply (div_le_iff₀ h2G).mp at htime
    apply (div_le_iff₀ hN2).mp at htime
    nlinarith
  have hsquare : N ^ 4 ≤ 4 * G ^ 2 * η ^ 2 := by
    nlinarith [sq_nonneg (N ^ 2 - 2 * G * η)]
  have hbound : N ^ 4 ≤ 4 * C ^ 2 * N ^ 2 * E * η ^ 2 := by
    calc
      N ^ 4 ≤ 4 * G ^ 2 * η ^ 2 := hsquare
      _ ≤ 4 * (C ^ 2 * N ^ 2 * E) * η ^ 2 := by gcongr
      _ = 4 * C ^ 2 * N ^ 2 * E * η ^ 2 := by ring
  have hden : 0 < 4 * C ^ 2 * η ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have hcancel : N ^ 2 * N ^ 2 ≤ N ^ 2 * (4 * C ^ 2 * E * η ^ 2) := by
    simpa [pow_four] using hbound
  have hcanceled := (mul_le_mul_left hN2).mp hcancel
  nlinarith

end Millennium.NavierStokes
