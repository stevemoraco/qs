import Mathlib

/-!
# Fourier output-capacity firewall

This file formalizes the finite real algebra behind a load-bearing restriction
on any packet embedding of a shell cascade into Navier--Stokes.

For one fixed Fourier output, Cauchy--Schwarz removes every apparent gain from
adding more convolution pairs at fixed input `ℓ²` energy.  Summing over `J`
outputs permits at most a square-root-of-`J` gain in the output `ℓ²` norm.
Thus a first-order Euler symbol of size `O(N)` can reach an `O(N²)` viscous
rate with bounded packet energies only if the active output bundle has
capacity at least `Ω(N²)`.

The file does not formalize Fourier analysis, the Leray projector, the Euler
symbol bound, packet construction, leakage cancellation, or Navier--Stokes.
-/

namespace Millennium.NavierStokes

/-- Fixed-output convolution ceiling.

If the scalar symbol coefficients `Γ i` are bounded by `L`, then one fixed
output coefficient has no multiplicity gain: its square is bounded by `L²`
times the two input `ℓ²` energies. -/
theorem fixedOutputConvolution_sq_le
    {ι : Type*} [Fintype ι]
    (Γ u v : ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hΓ : ∀ i, |Γ i| ≤ L) :
    (∑ i, Γ i * u i * v i) ^ 2
      ≤ L ^ 2 * (∑ i, (u i) ^ 2) * ∑ i, (v i) ^ 2 := by
  have hCauchy :
      (∑ i, (Γ i * u i) * v i) ^ 2
        ≤ (∑ i, (Γ i * u i) ^ 2) * ∑ i, (v i) ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => Γ i * u i) v)
  have hWeighted :
      (∑ i, (Γ i * u i) ^ 2)
        ≤ L ^ 2 * ∑ i, (u i) ^ 2 := by
    calc
      (∑ i, (Γ i * u i) ^ 2)
          ≤ ∑ i, (L * u i) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hΓsq : (Γ i) ^ 2 ≤ L ^ 2 :=
              sq_le_sq₀ (abs_nonneg _) hL (hΓ i)
            have hmul :=
              mul_le_mul_of_nonneg_right hΓsq (sq_nonneg (u i))
            simpa [mul_pow] using hmul
      _ = L ^ 2 * ∑ i, (u i) ^ 2 := by
            simp_rw [mul_pow]
            rw [← mul_sum]
  have hV : 0 ≤ ∑ i, (v i) ^ 2 := by
    exact Finset.sum_nonneg fun i hi => sq_nonneg (v i)
  calc
    (∑ i, Γ i * u i * v i) ^ 2
        ≤ (∑ i, (Γ i * u i) ^ 2) * ∑ i, (v i) ^ 2 := hCauchy
    _ ≤ (L ^ 2 * ∑ i, (u i) ^ 2) * ∑ i, (v i) ^ 2 :=
      mul_le_mul_of_nonneg_right hWeighted hV
    _ = L ^ 2 * (∑ i, (u i) ^ 2) * ∑ i, (v i) ^ 2 := by ring

/-- If every one of `J` output coordinates has squared size at most `B`, the
whole output bundle has squared `ℓ²` size at most `J B`. -/
theorem outputBundle_sq_le
    {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (B : ℝ)
    (hcoord : ∀ k, (w k) ^ 2 ≤ B) :
    ∑ k, (w k) ^ 2 ≤ (Fintype.card κ : ℝ) * B := by
  calc
    ∑ k, (w k) ^ 2 ≤ ∑ _k : κ, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact hcoord k
    _ = (Fintype.card κ : ℝ) * B := by simp

/-- Output-bundle convolution ceiling.

A family of `J` fixed outputs can gain at most a factor `sqrt J` in `ℓ²` over
the fixed-output Cauchy--Schwarz ceiling. -/
theorem outputBundleConvolution_sq_le
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (Γ : κ → ι → ℝ) (u v : ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hΓ : ∀ k i, |Γ k i| ≤ L) :
    ∑ k, (∑ i, Γ k i * u i * v i) ^ 2
      ≤ (Fintype.card κ : ℝ) *
          (L ^ 2 * (∑ i, (u i) ^ 2) * ∑ i, (v i) ^ 2) := by
  apply outputBundle_sq_le
  intro k
  exact fixedOutputConvolution_sq_le (Γ k) u v L hL (hΓ k)

/-- Capacity tax for matching a viscous rate.

If a packet mechanism has speed at least `N²`, while the squared speed is
bounded by `J C² N² E_u E_v`, then its effective output capacity must satisfy
`N² ≤ J C² E_u E_v`.  In particular, bounded constants and bounded packet
energies force `J = Ω(N²)`. -/
theorem capacity_required_for_viscous_rate
    (G J C N Eu Ev : ℝ)
    (hN : 0 < N)
    (hlower : N ^ 4 ≤ G ^ 2)
    (hupper : G ^ 2 ≤ J * C ^ 2 * N ^ 2 * Eu * Ev) :
    N ^ 2 ≤ J * C ^ 2 * Eu * Ev := by
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  have hmul :
      N ^ 2 * N ^ 2 ≤ N ^ 2 * (J * C ^ 2 * Eu * Ev) := by
    calc
      N ^ 2 * N ^ 2 = N ^ 4 := by ring
      _ ≤ G ^ 2 := hlower
      _ ≤ J * C ^ 2 * N ^ 2 * Eu * Ev := hupper
      _ = N ^ 2 * (J * C ^ 2 * Eu * Ev) := by ring
  exact (mul_le_mul_left hN2).mp hmul

/-- If an output bundle has capacity at most `W³`, the same viscous-rate tax
passes to the packet width.  This is the scalar source of the critical
`W^(3/2)` norm gain and the threshold `W³ = Ω(N²)`. -/
theorem widthCubed_required_for_viscous_rate
    (J W N A : ℝ)
    (hA : 0 ≤ A)
    (hcapacity : N ^ 2 ≤ J * A)
    (hwidth : J ≤ W ^ 3) :
    N ^ 2 ≤ W ^ 3 * A := by
  calc
    N ^ 2 ≤ J * A := hcapacity
    _ ≤ W ^ 3 * A := mul_le_mul_of_nonneg_right hwidth hA

/-- An exact integer-exponent master point for the broad-packet route.

Writing the carrier scale as `N=t⁴` and the three-dimensional packet width as
`W=t³`, the available cubic output capacity `W³=t⁹` strictly dominates the
necessary `N²=t⁸` threshold for every `t≥1`.  Simultaneously `W/N=1/t`, so
the relative shell-width tax tends to zero as `t` grows. -/
theorem quarticCarrier_cubicWidth_meets_capacity
    (t : ℝ) (ht : 1 ≤ t) :
    (t ^ 4) ^ 2 ≤ (t ^ 3) ^ 3 := by
  have hnonneg : 0 ≤ t ^ 8 * (t - 1) :=
    mul_nonneg (pow_nonneg t 8) (sub_nonneg.mpr ht)
  calc
    (t ^ 4) ^ 2 = t ^ 8 := by ring
    _ ≤ t ^ 9 := by nlinarith
    _ = (t ^ 3) ^ 3 := by ring

/-- At the same master point, the relative packet width is exactly `1/t`. -/
theorem quarticCarrier_cubicWidth_ratio
    (t : ℝ) (ht : 0 < t) :
    t ^ 3 / t ^ 4 = 1 / t := by
  field_simp [ne_of_gt ht]
  ring

#print axioms fixedOutputConvolution_sq_le
#print axioms outputBundle_sq_le
#print axioms outputBundleConvolution_sq_le
#print axioms capacity_required_for_viscous_rate
#print axioms widthCubed_required_for_viscous_rate
#print axioms quarticCarrier_cubicWidth_meets_capacity
#print axioms quarticCarrier_cubicWidth_ratio

end Millennium.NavierStokes
