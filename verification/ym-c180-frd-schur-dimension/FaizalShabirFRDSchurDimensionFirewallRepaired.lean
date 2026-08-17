import Mathlib

namespace Millennium.YangMills.FaizalShabirFRDSchurDimensionFirewall

theorem d3_source_decay_is_subvolume
    (eps : ℝ) (heps0 : 0 < eps) (heps2 : eps < 2) :
    0 < 2 - eps ∧ (2 - eps) < 3 ∧ 0 < 3 - (2 - eps) := by
  constructor
  · linarith
  constructor <;> linarith

theorem d3_net_exponent_identity (eps : ℝ) :
    (3 : ℝ) - (2 - eps) = 1 + eps := by
  ring

theorem eps_one_net_exponent :
    (3 : ℝ) - (2 - 1) = 2 := by
  norm_num

theorem eps_one_quadratic_envelope_grows
    (L : ℝ) (hL : 1 < L) :
    1 < L ^ 2 := by
  nlinarith

theorem eps_one_quadratic_envelope_unbounded
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ L : ℝ, 1 < L ∧ C < L ^ 2 := by
  refine ⟨C + 2, ?_, ?_⟩
  · linarith
  · nlinarith

theorem cubic_support_cubic_decay_zero_net_exponent :
    (3 : ℝ) - 3 = 0 := by
  norm_num

#print axioms d3_source_decay_is_subvolume
#print axioms d3_net_exponent_identity
#print axioms eps_one_net_exponent
#print axioms eps_one_quadratic_envelope_grows
#print axioms eps_one_quadratic_envelope_unbounded
#print axioms cubic_support_cubic_decay_zero_net_exponent

end Millennium.YangMills.FaizalShabirFRDSchurDimensionFirewall
