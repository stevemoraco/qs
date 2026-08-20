import Mathlib

/-!
# C328: parabolic center/stable cone finite firewall

Finite real-algebra consumers for the repaired Faizal--Shabir weak-RG architecture.

The file proves only:
* a cubic center step with remainder `|R| <= rho * g^3` lies between two
  cubic comparison steps;
* `rho < beta` leaves a positive effective cubic decrement;
* on the parabolic boundary `K = A g^2`, the mixed `g K` channel is exactly
  cubic order and therefore can shift the one-loop coefficient unless a
  stronger cancellation/subquadratic theorem is supplied.

It does not formalize the Yang--Mills Banach RG, an invariant cone, asymptotic
freedom, AF/IR identification, continuum OS reconstruction, a mass gap, or the
Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirParabolicConeHarmonicBootstrap

/-- A center step with an absolute cubic remainder lies between the two
comparison cubic steps. -/
theorem center_step_two_sided
    (g g' beta rho R : ℝ)
    (hstep : g' = g - beta * g ^ 3 + R)
    (hR : |R| ≤ rho * g ^ 3)
    (hg : 0 ≤ g) :
    g - (beta + rho) * g ^ 3 ≤ g' ∧
      g' ≤ g - (beta - rho) * g ^ 3 := by
  have hpow : 0 ≤ g ^ 3 := by positivity
  have hRlo : -(rho * g ^ 3) ≤ R := (abs_le.mp hR).1
  have hRhi : R ≤ rho * g ^ 3 := (abs_le.mp hR).2
  constructor
  · rw [hstep]
    nlinarith
  · rw [hstep]
    nlinarith

/-- A strict cubic remainder margin leaves a positive effective decrement. -/
theorem effective_cubic_margin_pos
    (beta rho : ℝ)
    (hmargin : rho < beta) :
    0 < beta - rho := by
  linarith

/-- On the parabolic boundary `K = A g^2`, the allowed mixed center channel
`g*K` is exactly cubic order. -/
theorem mixed_channel_is_cubic_on_parabolic_boundary
    (g A : ℝ) :
    g * (A * g ^ 2) = A * g ^ 3 := by
  ring

/-- The quadratic stable channel on the same boundary is fourth order. -/
theorem stable_square_is_quartic_on_parabolic_boundary
    (g A : ℝ) :
    (A * g ^ 2) ^ 2 = A ^ 2 * g ^ 4 := by
  ring

#print axioms center_step_two_sided
#print axioms effective_cubic_margin_pos
#print axioms mixed_channel_is_cubic_on_parabolic_boundary
#print axioms stable_square_is_quartic_on_parabolic_boundary

end Millennium.YangMills.FaizalShabirParabolicConeHarmonicBootstrap
