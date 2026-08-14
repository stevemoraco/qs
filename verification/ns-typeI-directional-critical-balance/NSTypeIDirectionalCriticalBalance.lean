import Mathlib

namespace Millennium.NavierStokes

/-!
# Type-I directional roughness critical-balance firewall

Finite exponent arithmetic and reusable scalar inequalities only.

The exponent bookkeeping corresponds to the Type-I parabolic scales

* length `r ~ tau^(1/2)`,
* vorticity `|omega| ~ tau^(-1)`,
* active volume `~ r^3 ~ tau^(3/2)`.

If the vorticity direction changes by order one across the natural length, then
`|grad omega|` has exponent `-3/2`. Consequently palinstrophy and Type-I
vortex stretching both have exponent `-3/2` after spatial integration. Thus
power counting alone has no positive exponent margin with which to absorb
stretching into viscosity.

There is a second scaling firewall. If one zooms to `r ~ tau^b`, the vorticity
amplitude after Navier--Stokes rescaling has Type-I exponent `2*b - 1`. At the
natural scale `b=1/2` this is neutral. Any strictly smaller physical scale has
`b>1/2`, hence positive exponent, so the Type-I-sized normalized vorticity tends
toward zero at the level of power counting. Thus one cannot simply zoom farther
until the direction is coherent while expecting Type-I scaling alone to retain
a nontrivial vorticity profile.

A successful directional route therefore needs coefficient depletion,
geometric cancellation, or a compactness theorem producing coherence at a
nontrivial normalization scale.

Nothing here asserts that these scalar exponents are realized or saturated by a
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

/-- Under Navier--Stokes scaling at `r ~ tau^b`, a Type-I vorticity amplitude
`tau^(-1)` becomes `r^2 omega`, with exponent `2*b-1`. At the natural scale
`b=1/2` this exponent is exactly zero. -/
theorem typeI_natural_zoom_vorticity_exponent :
    2 * (1 / 2 : ℚ) - 1 = 0 := by
  norm_num

/-- Every strictly sub-natural physical zoom `b>1/2` gives a positive exponent
for the normalized Type-I vorticity scale. -/
theorem typeI_subnatural_zoom_has_positive_vorticity_exponent
    {b : ℚ} (hb : 1 / 2 < b) :
    0 < 2 * b - 1 := by
  linarith

/-- Conversely, if the normalized Type-I vorticity power is not decaying, the
zoom exponent cannot be strictly sub-natural. -/
theorem typeI_nondecaying_vorticity_power_forces_nonsubnatural_zoom
    {b : ℚ} (hpower : 2 * b - 1 ≤ 0) :
    b ≤ 1 / 2 := by
  linarith

/-- What would actually be sufficient at the scalar energy level is a strict
coefficient depletion. If stretching is at most `(1-eta) * nu * D`, then the
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

/-- The coefficient margin survives a localization/forcing error that consumes
at most a `theta` fraction of the nominal depletion margin. -/
theorem coefficient_depletion_survives_relative_error
    {nu eta D stretching E theta : ℝ}
    (hstretch : stretching ≤ (1 - eta) * nu * D + E)
    (hE : E ≤ theta * eta * nu * D) :
    stretching - nu * D ≤ -((1 - theta) * eta * nu * D) := by
  calc
    stretching - nu * D ≤ ((1 - eta) * nu * D + E) - nu * D :=
      sub_le_sub_right hstretch _
    _ ≤ ((1 - eta) * nu * D + theta * eta * nu * D) - nu * D := by
      exact sub_le_sub_right (add_le_add_left hE _) _
    _ = -((1 - theta) * eta * nu * D) := by ring

/-- If the error uses a strict fraction `theta<1` of a positive depletion
margin, strict absorption remains. -/
theorem coefficient_depletion_with_error_is_strict
    {nu eta D stretching E theta : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (hD : 0 < D) (htheta : theta < 1)
    (hstretch : stretching ≤ (1 - eta) * nu * D + E)
    (hE : E ≤ theta * eta * nu * D) :
    stretching < nu * D := by
  have hthetaPos : 0 < 1 - theta := by linarith
  have hmargin : 0 < (1 - theta) * eta * nu * D := by positivity
  have h := coefficient_depletion_survives_relative_error hstretch hE
  linarith

/-- With strictly positive viscosity, depletion fraction and dissipation, the
zero-error coefficient estimate gives a genuinely strict absorption margin. -/
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
#print axioms typeI_natural_zoom_vorticity_exponent
#print axioms typeI_subnatural_zoom_has_positive_vorticity_exponent
#print axioms typeI_nondecaying_vorticity_power_forces_nonsubnatural_zoom
#print axioms coefficient_depletion_absorbs
#print axioms coefficient_depletion_survives_relative_error
#print axioms coefficient_depletion_with_error_is_strict
#print axioms coefficient_depletion_is_strict

end Millennium.NavierStokes
