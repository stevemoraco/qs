import Mathlib

/-!
# Faizal–Shabir center/stable marginal-contraction firewall

Finite real-algebra consumers for the source audit comparing:

* the Yang–Mills marginal coupling map `g ↦ g - β g^3 + ...`, whose
  linearization at `g = 0` is the identity; and
* a genuinely stable coordinate satisfying a quadratic recurrence
  `x' ≤ ρ x + C x^2` on a small ball.

The point is deliberately narrow. A fixed strict linear contraction `q < 1`
can be obtained from the quadratic recurrence on a bounded stable ball, but it
cannot uniformly dominate the cubic marginal map arbitrarily close to zero.
Therefore a repaired AF/IR proof must use a center–stable splitting: match the
marginal/two-loop transmutation coordinate at a fixed physical scale and use
strict contraction only on the irrelevant/stable coordinates.

This file does not formalize Yang–Mills fields, RG maps, Banach spaces,
Osterwalder–Schrader reconstruction, `Lambda_YM`, or any Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirCenterStableMarginalFirewall

/-- On a stable ball `0 ≤ x ≤ r`, the quadratic recurrence
`xnext ≤ rho*x + C*x^2` is dominated by the linear factor `rho + C*r`. -/
theorem stable_quadratic_step_contracts
    (rho C r x xnext : ℝ)
    (hC : 0 ≤ C)
    (hx : 0 ≤ x)
    (hxr : x ≤ r)
    (hstep : xnext ≤ rho * x + C * x ^ 2) :
    xnext ≤ (rho + C * r) * x := by
  have hxx : x * x ≤ r * x := mul_le_mul_of_nonneg_right hxr hx
  have hCxx : C * (x * x) ≤ C * (r * x) :=
    mul_le_mul_of_nonneg_left hxx hC
  nlinarith [hCxx]

/-- If `β g^2 < 1-q`, then the cubic marginal step `g - β g^3`
strictly exceeds `q*g`. Thus no fixed `q < 1` can dominate the marginal map
all the way down to arbitrarily small positive `g`. -/
theorem cubic_marginal_exceeds_strict_q
    (beta q g : ℝ)
    (hg : 0 < g)
    (hsmall : beta * g ^ 2 < 1 - q) :
    q * g < g - beta * g ^ 3 := by
  have hm := mul_lt_mul_of_pos_right hsmall hg
  nlinarith [hm]

/-- Conversely, if one insists that the cubic marginal step is bounded by
`q*g` at a positive `g`, then `β g^2` must already be at least `1-q`.
This is the finite obstruction to a regulator-independent strict `q < 1`
acting on the Yang–Mills marginal coordinate as `g → 0`. -/
theorem strict_q_on_cubic_requires_nonzero_scale
    (beta q g : ℝ)
    (hg : 0 < g)
    (hbound : g - beta * g ^ 3 ≤ q * g) :
    1 - q ≤ beta * g ^ 2 := by
  have hmul : (1 - q) * g ≤ (beta * g ^ 2) * g := by
    nlinarith [hbound]
  exact (mul_le_mul_right hg).mp hmul

#print axioms stable_quadratic_step_contracts
#print axioms cubic_marginal_exceeds_strict_q
#print axioms strict_q_on_cubic_requires_nonzero_scale

end Millennium.YangMills.FaizalShabirCenterStableMarginalFirewall
