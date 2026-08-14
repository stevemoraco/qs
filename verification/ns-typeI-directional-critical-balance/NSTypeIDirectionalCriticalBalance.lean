import Mathlib

namespace Millennium.NavierStokes

/-!
# Type-I directional roughness critical-balance firewall

Finite exponent arithmetic and a reusable scalar absorption inequality only.

The exponent bookkeeping corresponds to the Type-I parabolic scales

* length `r ~ tau^(1/2)`,
* vorticity `|omega| ~ tau^(-1)`,
* active volume `~ r^3 ~ tau^(3/2)`.

If the vorticity direction changes by order one across the natural length, then
`|grad omega|` has exponent `-3/2`.  Consequently palinstrophy and Type-I
vortex stretching both have exponent `-3/2` after spatial integration.  Thus
power counting alone has no positive exponent margin with which to absorb
stretching into viscosity.  A successful directional route needs an additional
coefficient depletion / geometric cancellation theorem, not merely Type-I
scaling.

Nothing here asserts that these scalar exponents are realized by a
Navier--Stokes solution, and no regularity or blow-up conclusion is encoded.
-/

/-- Natural Type-I enstrophy exponent:
`omega^2 * volume ~ tau^(-2 + 3/2) = tau^(-1/2)`. -/
theorem typeI_enstrophy_exponent :
    (-2 : ℚ) + 3 / 2 = -1 / 2 := by
  norm_num

/-- Order-one directional variation at natural scale gives
`grad omega ~ tau^(-1-1/2)`, hence integrated palinstrophy exponent `-3/2`. -/
theorem typeI_palinstrophy_exponent :
    2 * ((-1 : ℚ) - 1 / 2) + 3 / 2 = -3 / 2 := by
  norm_num

/-- Under a Type-I strain scale `|S| ~ tau^(-1)`, integrated vortex stretching
`S omega omega * volume` also has exponent `-3/2`. -/
theorem typeI_stretching_exponent :
    (-1 : ℚ) + 2 * (-1) + 3 / 2 = -3 / 2 := by
  norm_num

/-- The two load-bearing terms are exactly power-critical with respect to one
another at the natural Type-I scale. -/
theorem typeI_directional_roughness_is_power_critical :
    2 * ((-1 : ℚ) - 1 / 2) + 3 / 2 =
      (-1 : ℚ) + 2 * (-1) + 3 / 2 := by
  norm_num

/-- Equality of power exponents cannot by itself manufacture any strictly
positive power gain. -/
theorem equal_exponents_exclude_positive_power_gain
    {a delta : ℚ} (hdelta : 0 < delta) :
    ¬ (a + delta ≤ a) := by
  linarith

/-- Specialized firewall: no positive `tau^delta` depletion follows from the
Type-I power count alone, because both terms sit at exponent `-3/2`. -/
theorem typeI_scaling_has_no_positive_depletion_exponent
    {delta : ℚ} (hdelta : 0 < delta) :
    ¬ ((-3 / 2 : ℚ) + delta ≤ -3 / 2) := by
  exact equal_exponents_exclude_positive_power_gain hdelta

/-- What would actually be sufficient at the scalar energy level is a strict
coefficient depletion.  If stretching is at most `(1-eta) * nu * D`, then the
net stretching-minus-viscosity contribution retains `eta * nu * D` of
coercivity. -/
theorem coefficient_depletion_absorbs
    {nu eta D stretching : ℝ}
    (hstretch : stretching ≤ (1 - eta) * nu * D) :
    stretching - nu * D ≤ -(eta * nu * D) := by
  calc
    stretching - nu * D ≤ (1 - eta) * nu * D - nu * D :=
      sub_le_sub_right hstretch _
    _ = -(eta * nu * D) := by ring

/-- With strictly positive viscosity, depletion fraction and dissipation, the
same coefficient estimate gives a genuinely strict absorption margin. -/
theorem coefficient_depletion_is_strict
    {nu eta D stretching : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (hD : 0 < D)
    (hstretch : stretching ≤ (1 - eta) * nu * D) :
    stretching < nu * D := by
  have hmargin : 0 < eta * nu * D := by positivity
  have h := coefficient_depletion_absorbs hstretch
  linarith

#print axioms typeI_enstrophy_exponent
#print axioms typeI_palinstrophy_exponent
#print axioms typeI_stretching_exponent
#print axioms typeI_directional_roughness_is_power_critical
#print axioms equal_exponents_exclude_positive_power_gain
#print axioms typeI_scaling_has_no_positive_depletion_exponent
#print axioms coefficient_depletion_absorbs
#print axioms coefficient_depletion_is_strict

end Millennium.NavierStokes
