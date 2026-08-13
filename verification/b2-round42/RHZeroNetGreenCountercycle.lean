import Mathlib

/-!
# Zero-net Green-energy countercycle

This file formalizes only the finite three-step recurrence and energy loss used
in the round-42 RH audit. It does not formalize logarithms, continuous arrival
existence, primes, Chebyshev functions, Johnston's criterion, zeta, or RH.
-/

namespace MillenniumBraid
namespace B2Round42RH

/-- Three centered increments with zero total forcing. -/
theorem three_step_forcing_zero_net (d : ℝ) :
    (-d) + (-d) + 2 * d = 0 := by
  ring

/-- Exact three-step mismatch states generated from zero by increments
`-d,-d,2d`. -/
theorem three_step_state_cycle (d : ℝ) :
    let z0 : ℝ := 0
    let z1 := z0 - d
    let z2 := z1 - d
    let z3 := z2 + 2 * d
    z1 = -d ∧ z2 = -2 * d ∧ z3 = z0 := by
  dsimp
  constructor
  · ring
  constructor <;> ring

/-- The endpoint returns exactly although the two intermediate states are
negative. -/
theorem zero_net_returns_endpoint (d : ℝ) :
    (((0 : ℝ) - d) - d) + 2 * d = 0 := by
  ring

/-- Exact weighted energy identity for the three-step countercycle. -/
theorem three_step_energy_identity
    (d L1 L2 L3 : ℝ) :
    L1 * (-d) + L2 * (-2 * d) + L3 * 0 =
      -d * (L1 + 2 * L2) := by
  ring

/-- Positive depth and positive first two logarithmic weights force a strict
negative block-energy increment even though the endpoint state returns. -/
theorem three_step_energy_strictly_negative
    {d L1 L2 L3 : ℝ}
    (hd : 0 < d) (hL1 : 0 < L1) (hL2 : 0 < L2) :
    L1 * (-d) + L2 * (-2 * d) + L3 * 0 < 0 := by
  have hsum : 0 < L1 + 2 * L2 := by positivity
  rw [three_step_energy_identity]
  nlinarith [mul_pos hd hsum]

/-- Endpoint equality and zero net forcing do not imply nonnegative energy:
an explicit finite witness packages all three facts. -/
theorem endpoint_noncollapse_does_not_preserve_energy
    (d L1 L2 L3 : ℝ)
    (hd : 0 < d) (hL1 : 0 < L1) (hL2 : 0 < L2) :
    (-d) + (-d) + 2 * d = 0 ∧
      (((0 : ℝ) - d) - d) + 2 * d = 0 ∧
      L1 * (-d) + L2 * (-2 * d) + L3 * 0 < 0 := by
  exact ⟨three_step_forcing_zero_net d,
    zero_net_returns_endpoint d,
    three_step_energy_strictly_negative hd hL1 hL2⟩

#print axioms three_step_forcing_zero_net
#print axioms three_step_state_cycle
#print axioms zero_net_returns_endpoint
#print axioms three_step_energy_identity
#print axioms three_step_energy_strictly_negative
#print axioms endpoint_noncollapse_does_not_preserve_energy

end B2Round42RH
end MillenniumBraid
