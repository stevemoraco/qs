import Mathlib

/-!
# Faizal--Shabir FRD Schur dimension firewall

Finite real-algebra checks for a hostile audit of the claimed scale-uniform
`ℓ¹` kernel row in arXiv:2606.19362v1 Appendix C.

The manuscript combines three-dimensional support volume `O(L^3)` with an
operator-norm decay `O(L^{-(2-eps)})`, `0 < eps < 2`, and states that this
crude support-counting/Schur route gives a scale-uniform row bound.  The net
power is instead `3 - (2-eps) = 1 + eps > 0`.

At the admissible witness `eps = 1`, the crude envelope is exactly
`L^3 * L⁻¹ = L^2`, hence is unbounded as `L` grows.  This does **not** prove
that the actual FRD kernel row is unbounded; it proves only that finite range
plus the displayed operator-norm decay cannot establish the claimed uniform
row by the printed counting argument.  A repair needs stronger pointwise
kernel decay/cancellation or a differently scaled row norm.

This file does not formalize Yang--Mills fields, finite-range decomposition,
Schur's test, transfer operators, OS reconstruction, a mass gap, or a Clay
theorem.
-/

namespace Millennium.YangMills.FaizalShabirFRDSchurDimensionFirewall

/-- In dimension three, the manuscript's exponent `2 - eps` is positive but
strictly smaller than the support-volume exponent `3`, leaving positive net
power `1 + eps`. -/
theorem d3_source_decay_is_subvolume
    (eps : ℝ)
    (heps0 : 0 < eps)
    (heps2 : eps < 2) :
    0 < 2 - eps ∧ (2 - eps) < 3 ∧ 0 < 3 - (2 - eps) := by
  constructor
  · linarith
  constructor <;> linarith

/-- Exact net exponent identity behind the dimension audit. -/
theorem d3_net_exponent_identity (eps : ℝ) :
    (3 : ℝ) - (2 - eps) = 1 + eps := by
  ring

/-- The admissible witness `eps = 1` makes the printed operator-norm decay
scale like `L⁻¹`; multiplying by a three-dimensional support count `L^3`
leaves `L^2`. -/
theorem eps_one_volume_times_decay
    (L : ℝ)
    (hL : 0 < L) :
    L ^ 3 * L⁻¹ = L ^ 2 := by
  field_simp [ne_of_gt hL]
  <;> ring

/-- For every scale factor above one, the `eps = 1` crude Schur envelope is
already larger than one. -/
theorem eps_one_crude_schur_grows
    (L : ℝ)
    (hL : 1 < L) :
    1 < L ^ 3 * L⁻¹ := by
  have hLpos : 0 < L := lt_trans zero_lt_one hL
  rw [eps_one_volume_times_decay L hLpos]
  nlinarith

/-- The printed support-volume-times-operator-norm envelope has no uniform
finite bound at the admissible witness `eps = 1`. -/
theorem eps_one_crude_schur_unbounded
    (C : ℝ)
    (hC : 0 ≤ C) :
    ∃ L : ℝ, 1 < L ∧ C < L ^ 3 * L⁻¹ := by
  refine ⟨C + 2, ?_, ?_⟩
  · linarith
  · have hLpos : 0 < C + 2 := by linarith
    rw [eps_one_volume_times_decay (C + 2) hLpos]
    nlinarith

/-- By contrast, cubic pointwise decay would exactly cancel a cubic support
count in this scalar envelope.  This records one sufficient scaling target
for the same crude counting route, not a claim that the QFT kernel has it. -/
theorem cubic_support_cubic_decay_cancels
    (L : ℝ)
    (hL : 0 < L) :
    L ^ 3 * (L ^ 3)⁻¹ = 1 := by
  field_simp [ne_of_gt hL]

#print axioms d3_source_decay_is_subvolume
#print axioms d3_net_exponent_identity
#print axioms eps_one_volume_times_decay
#print axioms eps_one_crude_schur_grows
#print axioms eps_one_crude_schur_unbounded
#print axioms cubic_support_cubic_decay_cancels

end Millennium.YangMills.FaizalShabirFRDSchurDimensionFirewall
