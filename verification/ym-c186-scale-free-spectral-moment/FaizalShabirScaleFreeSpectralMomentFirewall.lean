import Mathlib

/-!
# Scale-free extra spectral moment firewall

Finite real-algebra firewall for the C185A proposed repair of the Faizal--Shabir
UV remainder.  C185A observes that a second spectral multiplier moment can give
an inverse-square large-scale tail *if* the interacting irrelevant remainder
supplies one additional spectral factor with a regulator/volume/scale-uniform
coefficient.

This file records why that uniform coefficient is load-bearing.  On a soft
spectral mode of size `lambda > 0`, upgrading one power of `lambda` to two powers
requires a coefficient at least `1/lambda` unless the extra factor is intrinsic.
A Poincare-style recovery whose constant scales like the inverse spectral edge
is therefore exactly critical: it can erase the inverse-square gain rather than
produce it.

This file does not formalize the connection Laplacian, Bauerschmidt's theorem,
Proj_G, polymer RG, BKAR, Yang--Mills, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirScaleFreeSpectralMomentFirewall

/-- If a normalized soft-mode upgrade requires `1 <= C * lambda`, then the
coefficient is at least the inverse spectral scale. -/
theorem extra_moment_coefficient_lower_bound
    (lambda C : ℝ)
    (hlambda : 0 < lambda)
    (hupgrade : 1 ≤ C * lambda) :
    1 / lambda ≤ C := by
  exact (div_le_iff₀ hlambda).2 hupgrade

/-- More generally, controlling a positive amplitude by one spectral factor
forces the relative coefficient to dominate `amplitude / lambda`. -/
theorem spectral_factor_relative_cost
    (amplitude lambda C : ℝ)
    (hlambda : 0 < lambda)
    (hcontrol : amplitude ≤ C * lambda) :
    amplitude / lambda ≤ C := by
  exact (div_le_iff₀ hlambda).2 hcontrol

/-- A fixed coefficient cannot upgrade a unit normalized soft remainder through
an arbitrarily small spectral factor: whenever `C * lambda < 1`, the required
normalized inequality fails. -/
theorem soft_mode_breaks_fixed_extra_factor
    (lambda C : ℝ)
    (hsmall : C * lambda < 1) :
    ¬ (1 ≤ C * lambda) := by
  exact not_le_of_gt hsmall

/-- If a block-scale Poincare recovery costs `T^2` while the available spectral
gain is `lambda` with `T^2 * lambda = 1`, then the putative gain is exactly
critical rather than decaying. -/
theorem poincare_scale_exactly_cancels_spectral_gain
    (T lambda : ℝ)
    (hcritical : T ^ 2 * lambda = 1) :
    T ^ 2 * lambda = 1 :=
  hcritical

/-- The same criticality can be written in the opposite commutative order. -/
theorem inverse_edge_cost_times_edge_is_one
    (T lambda : ℝ)
    (hcritical : T ^ 2 * lambda = 1) :
    lambda * T ^ 2 = 1 := by
  calc
    lambda * T ^ 2 = T ^ 2 * lambda := by ring
    _ = 1 := hcritical

/-- By contrast, a genuinely scale-uniform coefficient preserves a small
spectral gain.  This is the finite consumer needed after an analytic theorem
supplies an intrinsic extra spectral factor. -/
theorem uniform_factor_preserves_small_gain
    (factor factorMax lambda gainMax : ℝ)
    (hfactor : factor ≤ factorMax)
    (hlambda : lambda ≤ gainMax)
    (hlambda_nonneg : 0 ≤ lambda)
    (hfactorMax_nonneg : 0 ≤ factorMax) :
    factor * lambda ≤ factorMax * gainMax := by
  exact mul_le_mul hfactor hlambda hlambda_nonneg hfactorMax_nonneg

/-- Package: an inverse-edge-sized recovery constant together with an
inverse-square spectral gain leaves an order-one normalized factor. -/
theorem inverse_edge_recovery_is_critical
    (recovery spectralGain : ℝ)
    (hproduct : recovery * spectralGain = 1) :
    recovery * spectralGain = 1 :=
  hproduct

#print axioms extra_moment_coefficient_lower_bound
#print axioms spectral_factor_relative_cost
#print axioms soft_mode_breaks_fixed_extra_factor
#print axioms poincare_scale_exactly_cancels_spectral_gain
#print axioms inverse_edge_cost_times_edge_is_one
#print axioms uniform_factor_preserves_small_gain
#print axioms inverse_edge_recovery_is_critical

end Millennium.YangMills.FaizalShabirScaleFreeSpectralMomentFirewall
