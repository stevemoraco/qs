import Mathlib

/-!
# Fast-activation conjugate-sideband finite firewall

This file formalizes only the scalar response bookkeeping and exponent signs
used in the round-42 Navier--Stokes audit. It does not formalize the heat
semigroup, Fourier triads, Leray projection, Palasek's shell model, the
Navier--Stokes equations, or a blow-up theorem.
-/

namespace MillenniumBraid
namespace B2Round42NS

/-- The explicit Palasek parameter point has activation exponent strictly
faster than the carrier heat exponent. -/
theorem explicit_fast_activation_exponent :
    2 * (17 / 16 : ℚ) - 35 / 16 = -1 / 16 := by
  norm_num

/-- In particular the carrier-time product has a negative power exponent. -/
theorem explicit_fast_activation_exponent_negative :
    2 * (17 / 16 : ℚ) - 35 / 16 < 0 := by
  norm_num

/-- General scalar sign: `beta > 2*b` is exactly the negative exponent
condition for `K^2*tau`. -/
theorem fast_activation_exponent_negative
    {b beta : ℝ} (hfast : 2 * b < beta) :
    2 * b - beta < 0 := by
  linarith

/-- If a sideband forcing integrates to the same feed `X` over an activation
interval, and its exact heat attenuation factor is at least one half, then the
terminal sideband correction is at least half the principal feed. -/
theorem equal_feed_with_half_attenuation_is_order_one
    {X tau E attenuation response : ℝ}
    (hX : 0 ≤ X)
    (hfeed : tau * E = X)
    (hatt : 1 / 2 ≤ attenuation)
    (hresponse : response = attenuation * (tau * E)) :
    X / 2 ≤ response := by
  rw [hresponse, hfeed]
  nlinarith

/-- The same statement in ratio-free product form. -/
theorem half_attenuation_product_lower_bound
    {X attenuation : ℝ}
    (hX : 0 ≤ X)
    (hatt : 1 / 2 ≤ attenuation) :
    X / 2 ≤ attenuation * X := by
  nlinarith

/-- Exact bookkeeping: a feed rate `E=X/tau` integrated over `tau` is `X`.
The nonzero hypothesis prevents an illegal division by zero. -/
theorem feed_rate_integrates_to_principal
    {X tau E : ℝ}
    (htau : tau ≠ 0)
    (hE : E = X / tau) :
    tau * E = X := by
  rw [hE]
  field_simp [htau]

/-- A putative power-small upper bound below one half contradicts the exact
order-one lower response. -/
theorem no_subhalf_relative_bound
    {X response epsilon : ℝ}
    (hX : 0 < X)
    (hlower : X / 2 ≤ response)
    (heps : epsilon < 1 / 2)
    (hupper : response ≤ epsilon * X) :
    False := by
  nlinarith

#print axioms explicit_fast_activation_exponent
#print axioms explicit_fast_activation_exponent_negative
#print axioms fast_activation_exponent_negative
#print axioms equal_feed_with_half_attenuation_is_order_one
#print axioms half_attenuation_product_lower_bound
#print axioms feed_rate_integrates_to_principal
#print axioms no_subhalf_relative_bound

end B2Round42NS
end MillenniumBraid
