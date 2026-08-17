import Mathlib

/-!
# RH B273 Suzuki/B46 five-point finite core

Finite companion to `stevemoraco/RH#1494` / B273.

This file formalizes only the load-bearing scalar algebra behind the exact
five-point bridge:

* the Laurent-symbol factorization after clearing `z⁻²`;
* zero total mass and zero first offset moment of the five-point packet;
* the factorization of the five-point stencil as a discrete Laplacian of the
  half-exponential-neutral three-point operator;
* the exact two-frequency anchor cancellation used by the hostile firewall;
* strict nonvanishing of that hostile output away from the anchor for `c>0`.

It does **not** formalize distributions, convolutions, Suzuki's `g₀`, prime
powers, von Mangoldt weights, Mellin/Laplace transforms, zeta, BGST, B46's
analytic contraction, RH, or not-RH.
-/

namespace RHB273SuzukiB46FivePointFinite

/-- The B273 five-point Laurent symbol after multiplication by `z^2`. -/
theorem fivePointSymbolFactor (c z : ℚ) :
    -c * (z ^ 4 + 1)
      + (1 + c) ^ 2 * (z ^ 3 + z)
      - 2 * (1 + c + c ^ 2) * z ^ 2
      = -(z - c) * (z - 1) ^ 2 * (c * z - 1) := by
  ring

/-- The five slope-jump coefficients have total mass zero. -/
theorem fivePointMassZero (c : ℚ) :
    -c + (1 + c) ^ 2 - 2 * (1 + c + c ^ 2) + (1 + c) ^ 2 - c = 0 := by
  ring

/-- The symmetric five-point packet also has zero first offset moment. -/
theorem fivePointFirstMomentZero (c : ℚ) :
    (-2 : ℚ) * (-c)
      + (-1 : ℚ) * (1 + c) ^ 2
      + (1 : ℚ) * (1 + c) ^ 2
      + (2 : ℚ) * (-c) = 0 := by
  ring

/--
The five-point stencil equals the discrete Laplacian of
`(1+c^2) f(t) - c(f(t+h)+f(t-h))`.
-/
theorem fivePointDeltaFactor
    (c fm2 fm1 f0 fp1 fp2 : ℚ) :
    ((1 + c ^ 2) * fp1 - c * (fp2 + f0))
      - 2 * ((1 + c ^ 2) * f0 - c * (fp1 + fm1))
      + ((1 + c ^ 2) * fm1 - c * (f0 + fm2))
      = -c * (fm2 + fp2)
        + (1 + c) ^ 2 * (fm1 + fp1)
        - 2 * (1 + c + c ^ 2) * f0 := by
  ring

/--
Exact anchor cancellation for the even two-frequency hostile witness.
The frequency-`π/h` eigenvalue is `-4(1+c)^2`; the frequency-`π/(2h)`
eigenvalue is `-2(1+c^2)`. Scaling the two modes as below cancels at `t=0`.
-/
theorem hostileAnchorCancellation (c : ℚ) :
    (-4 * (1 + c) ^ 2) * (1 + c ^ 2)
      - (-2 * (1 + c ^ 2)) * (2 * (1 + c) ^ 2) = 0 := by
  ring

/-- The same hostile two-frequency output is genuinely nonzero at `t=h`. -/
theorem hostileOffAnchorPositive (c : ℚ) (hc : 0 < c) :
    0 < 4 * (1 + c) ^ 2 * (1 + c ^ 2) := by
  positivity

#print axioms fivePointSymbolFactor
#print axioms fivePointMassZero
#print axioms fivePointFirstMomentZero
#print axioms fivePointDeltaFactor
#print axioms hostileAnchorCancellation
#print axioms hostileOffAnchorPositive

end RHB273SuzukiB46FivePointFinite
