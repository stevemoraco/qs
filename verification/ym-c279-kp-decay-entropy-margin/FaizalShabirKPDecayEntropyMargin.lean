import Mathlib

/-!
# Faizal–Shabir KP decay-over-entropy margin firewall

Finite real-algebra shadow of the summation around Eq. (5.40) in
arXiv:2606.19362v1.

The source's diameter sum contains the factor
`exp ((cEntropy - cDecay) * m)`.  If the decay exponent does not strictly beat
the polymer-counting exponent, these terms do not even tend below one.  The
small activity prefactor cannot repair that missing exponent margin.

This file does not formalize polymer enumeration, KP, BKAR, RG, Yang–Mills,
OS reconstruction, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirKPDecayEntropyMargin

/-- If the claimed decay exponent is no larger than the entropy exponent, the
positive diameter factor is at least one for every nonnegative diameter. -/
theorem diameter_factor_not_decaying
    (m cDecay cEntropy : ℝ)
    (hm : 0 ≤ m)
    (hmargin : cDecay ≤ cEntropy) :
    1 ≤ Real.exp ((cEntropy - cDecay) * m) := by
  have hdiff : 0 ≤ cEntropy - cDecay := sub_nonneg.mpr hmargin
  have hexpnonneg : 0 ≤ (cEntropy - cDecay) * m := mul_nonneg hdiff hm
  simpa using (Real.one_le_exp hexpnonneg)

/-- A strict decay-over-entropy margin makes the diameter factor strictly less
than one at every strictly positive diameter. -/
theorem strict_margin_gives_pointwise_decay
    (m cDecay cEntropy : ℝ)
    (hm : 0 < m)
    (hmargin : cEntropy < cDecay) :
    Real.exp ((cEntropy - cDecay) * m) < 1 := by
  have hdiff : cEntropy - cDecay < 0 := sub_neg.mpr hmargin
  have hneg : (cEntropy - cDecay) * m < 0 := mul_neg_of_neg_of_pos hdiff hm
  simpa using (Real.exp_lt_one_iff.mpr hneg)

#print axioms diameter_factor_not_decaying
#print axioms strict_margin_gives_pointwise_decay

end Millennium.YangMills.FaizalShabirKPDecayEntropyMargin
