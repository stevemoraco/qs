import Mathlib

/-!
# Stable/marginal inverse-coupling power threshold

Finite exponent bookkeeping for C326.

If a stable coordinate has size `K = O(g^p)`, the two stable contributions
identified by the source audit scale as `g^(p-2)` and `g^(2p-3)` in the
inverse-coupling increment. Along `g ~ k^(-1/2)`, absolute p-series
summability requires `(p-2)/2 > 1` and `(2p-3)/2 > 1` respectively.

This file proves only that exponent algebra. It does not formalize an RG
trajectory, asymptotic freedom, summability of the actual Yang--Mills terms,
AF/IR identification, a mass gap, or the Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirStableMarginalPowerThreshold

theorem first_channel_threshold (p : ℝ) :
    (1 : ℝ) < (p - 2) / 2 ↔ 4 < p := by
  constructor <;> intro h <;> linarith

theorem second_channel_threshold (p : ℝ) :
    (1 : ℝ) < (2 * p - 3) / 2 ↔ (5 : ℝ) / 2 < p := by
  constructor <;> intro h <;> linarith

theorem p_four_first_channel_is_harmonic :
    (((4 : ℝ) - 2) / 2) = 1 := by
  norm_num

theorem p_five_first_channel_exponent :
    (((5 : ℝ) - 2) / 2) = (3 : ℝ) / 2 := by
  norm_num

theorem p_five_second_channel_exponent :
    ((2 * (5 : ℝ) - 3) / 2) = (7 : ℝ) / 2 := by
  norm_num

#print axioms first_channel_threshold
#print axioms second_channel_threshold
#print axioms p_four_first_channel_is_harmonic
#print axioms p_five_first_channel_exponent
#print axioms p_five_second_channel_exponent

end Millennium.YangMills.FaizalShabirStableMarginalPowerThreshold
