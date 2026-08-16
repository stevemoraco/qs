import Mathlib

/-!
# RH B191 mean-Mertens persistence finite core

Finite real/order algebra only.

This file formalizes the new deterministic scalar shell used by B191 after the
external analytic input supplies a power-deep negative first Mertens mean and the
prime number theorem supplies an eventual unit Lipschitz bound:

* moving by at most one quarter of the depth leaves at least three quarters of
  that negative depth;
* the resulting symmetric interval has the exact scalar negative-area ledger
  `3 * D^2 / 8`;
* a three-quarter surviving depth crosses any catastrophic threshold `T` once
  `4*T < 3*D`.

It deliberately does **not** formalize Zhao's theorem, the prime number theorem,
Mertens sums, integrals, primes, zeta zeros, BGST/Hermite theory, the B46
contraction, or the Riemann hypothesis.  The run/count exponent shell is already
formalized in the parent B158 finite branch and is not duplicated here.
-/

namespace RHMeanMertensPersistenceFinite

/-- If a value is at most `-D` and the total one-sided transport budget is at
most `D/4`, the transported value is still at most `-3D/4`. -/
theorem quarter_depth_transport_preserves_three_quarters
    {D f0 fy move : ℝ}
    (hD : 0 ≤ D)
    (hmove0 : 0 ≤ move)
    (hmove : move ≤ D / 4)
    (hf0 : f0 ≤ -D)
    (htransport : fy ≤ f0 + move) :
    fy ≤ -(3 * D / 4) := by
  linarith

/-- Exact scalar ledger for a symmetric interval of radius `D/4` carrying
surviving negative depth `3D/4`: its guaranteed negative area is `3D^2/8`. -/
theorem quarter_radius_area_ledger (D : ℝ) :
    (2 * (D / 4)) * (3 * D / 4) = 3 * D ^ 2 / 8 := by
  ring

/-- If the surviving three-quarter depth is strictly larger than a chosen
catastrophic threshold `T`, the transported value lies strictly below `-T`. -/
theorem three_quarters_depth_beats_threshold
    {D T fy : ℝ}
    (hdepth : 4 * T < 3 * D)
    (hfy : fy ≤ -(3 * D / 4)) :
    fy < -T := by
  linarith

#print axioms quarter_depth_transport_preserves_three_quarters
#print axioms quarter_radius_area_ledger
#print axioms three_quarters_depth_beats_threshold

end RHMeanMertensPersistenceFinite
