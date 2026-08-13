import Mathlib

/-!
# Packet-volume return gate: finite scalar core

This file formalizes only:

* two square-root convolution gains multiplying to the cell volume;
* the active coefficient/volume square identity;
* an exact counterexample to the volume-free return gate;
* the corrected packet-volume gate as an iff inequality; and
* the strengthened recursive scale implication.

It does not formalize Fourier convolution estimates, Navier--Stokes packet
symbols, heat flow, trapping, shadowing, or blow-up.
-/

namespace NSGolayPacketVolume

noncomputable section

/-- Scalar packet first-loop factor after restoring two convolution gains. -/
def packetLoop (r V nu N theta : ℝ) : ℝ :=
  r * V / (nu * N * theta ^ 2)

/-- BANKER: two normalized convolution gains `sqrt(V)` multiply to `V`. -/
theorem two_sqrt_volume_gains (V : ℝ) (hV : 0 ≤ V) :
    Real.sqrt V * Real.sqrt V = V := by
  nlinarith [Real.sq_sqrt hV]

/-- If the active coefficient is `c=r*G` and `G²=V`, then its square charges
exactly the volume factor `r²V`. -/
theorem active_gain_square_identity
    (r G V c : ℝ) (hG : G ^ 2 = V) (hc : c = r * G) :
    c ^ 2 = r ^ 2 * V := by
  rw [hc]
  calc
    (r * G) ^ 2 = r ^ 2 * G ^ 2 := by ring
    _ = r ^ 2 * V := by rw [hG]

/-- CRITIC: the volume-free quadratic separation can grow while the true
packet loop remains exactly one. -/
theorem old_quadratic_gate_can_miss_packet_volume
    (m : ℝ) (hm : 1 < m) :
    let r := 1
    let V := m
    let N := m ^ 3
    let theta := m⁻¹
    r < N * theta ^ 2 ∧
      r * V / (N * theta ^ 2) = 1 := by
  dsimp
  have hm0 : m ≠ 0 := by nlinarith
  have hscale : m ^ 3 * (m⁻¹) ^ 2 = m := by
    field_simp [hm0]
  rw [hscale]
  constructor
  · exact hm
  · field_simp [hm0]

/-- CLEANER: the corrected packet-volume separation budget is exactly
 equivalent to the desired loop bound. -/
theorem packet_loop_le_iff_volume_separation
    (r V nu N theta epsilon : ℝ)
    (hnu : 0 < nu) (hN : 0 < N) (htheta : 0 < theta) :
    packetLoop r V nu N theta ≤ epsilon ↔
      r * V ≤ epsilon * (nu * N * theta ^ 2) := by
  unfold packetLoop
  have hden : 0 < nu * N * theta ^ 2 := by positivity
  exact div_le_iff₀ hden

/-- The old plane-wave gate is the special case `V=1`. -/
theorem unit_volume_recovers_plane_wave_gate
    (r nu N theta : ℝ) :
    packetLoop r 1 nu N theta = r / (nu * N * theta ^ 2) := by
  unfold packetLoop
  ring

/-- The strengthened recursive scale budget absorbs the cell volume and
still yields a sixth-power margin. -/
theorem volume_scale_budget_gives_sixth_power_margin
    (K r V M : ℝ)
    (hK : 0 < K) (hM : 0 < M)
    (hscale : r * V * M ^ 8 ≤ K) :
    r * V * M ^ 2 / K ≤ 1 / M ^ 6 := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hM6 : 0 < M ^ 6 := by positivity
  have hpow : r * V * M ^ 2 * M ^ 6 ≤ K := by
    calc
      r * V * M ^ 2 * M ^ 6 = r * V * M ^ 8 := by ring
      _ ≤ K := hscale
  have hdiv : r * V * M ^ 2 ≤ K / M ^ 6 :=
    (le_div_iff₀ hM6).2 hpow
  apply (div_le_iff₀ hK).2
  calc
    r * V * M ^ 2 ≤ K / M ^ 6 := hdiv
    _ = (1 / M ^ 6) * K := by
      field_simp [hM0]

#print axioms two_sqrt_volume_gains
#print axioms active_gain_square_identity
#print axioms old_quadratic_gate_can_miss_packet_volume
#print axioms packet_loop_le_iff_volume_separation
#print axioms unit_volume_recovers_plane_wave_gate
#print axioms volume_scale_budget_gives_sixth_power_margin

end

end NSGolayPacketVolume
