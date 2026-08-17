import Mathlib

/-!
# Faizal--Shabir fixed-physical-time collar firewalls

Finite scalar/order-theoretic countermodels isolated while auditing the
fixed-physical-time Appendix-D repair of arXiv:2606.19362v1.

These declarations do not formalize Yang--Mills, OS Hilbert spaces, BKAR,
finite-range decompositions, or any continuum theorem. They record only three
load-bearing logical facts:

* positivity of a subtracted term does not justify dropping it inside a norm;
* an adjacent edge lies inside every collar of radius at least one without
  having separation larger than the collar radius;
* the k = 0 member of an exp(-c b^k) defect envelope is independent of b.
-/

namespace Millennium.YangMills.FaizalShabirFixedTauCollarFirewall

/-- Even with a nonnegative subtracted scalar `D`, subtraction can increase
absolute value. Hence `D ≥ 0` alone cannot justify
`|A - D + E| ≤ |A| + |E|`. -/
theorem positive_subtraction_cannot_be_dropped_from_norm :
    ∃ A D E : ℝ, 0 ≤ D ∧ |A - D + E| > |A| + |E| := by
  refine ⟨0, 1, 0, ?_, ?_⟩
  · norm_num
  · norm_num

/-- A nearest-neighbour separation of one is contained in every positive
integer collar but never exceeds that collar radius. Thus collar support by
itself does not imply the long-separation hypothesis needed for an
`exp (-c R)` factor. -/
theorem adjacent_edge_inside_collar_is_not_long
    (R : ℕ) (hR : 1 ≤ R) :
    1 ≤ R ∧ ¬ R < 1 := by
  exact ⟨hR, not_lt_of_ge hR⟩

/-- In an envelope `exp (-c * b^k)`, the zeroth-scale term is independent of
the block factor `b`. Increasing `b` cannot make this first term smaller
without additional `b`-dependence in the constants or a later starting scale. -/
theorem zeroth_scale_exponential_is_block_independent
    (b c : ℝ) :
    Real.exp (-c * b ^ (0 : ℕ)) = Real.exp (-c) := by
  simp

/-- The elementary fixed-physical-time gap budget: a total defect strictly
smaller than the initial transfer gap leaves a positive remainder. -/
theorem fixed_tau_positive_remainder
    (initialGap totalDefect : ℝ)
    (h : totalDefect < initialGap) :
    0 < initialGap - totalDefect := by
  exact sub_pos.mpr h

#print axioms positive_subtraction_cannot_be_dropped_from_norm
#print axioms adjacent_edge_inside_collar_is_not_long
#print axioms zeroth_scale_exponential_is_block_independent
#print axioms fixed_tau_positive_remainder

end Millennium.YangMills.FaizalShabirFixedTauCollarFirewall
