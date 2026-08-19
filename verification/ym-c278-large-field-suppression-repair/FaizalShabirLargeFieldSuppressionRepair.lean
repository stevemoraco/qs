import Mathlib

/-!
# Faizal–Shabir large-field suppression repair

Finite real-algebra firewall for the large-field step around Eqs. (5.26)–(5.28)
of arXiv:2606.19362v1.

The source's displayed union-bound calculation does not turn a one-plaquette
factor `q` into the block product `q^N`.  The first theorem records the smallest
exact witness.

The second theorem records the correct scalar monotonicity used by the repaired
large-field argument: if a bad event forces the total nonnegative penalty above
a fixed threshold, then its exponential regulator is bounded pointwise by the
threshold regulator.

This file deliberately does not formalize Haar measure, plaquette geometry,
Cauchy–Schwarz, polymer expansions, RG, OS reconstruction, Yang–Mills theory,
or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirLargeFieldSuppressionRepair

/-- Two one-plaquette union-bound contributions of size `1/2` do not imply the
product-style block bound `(1/2)^2`.  This is the finite arithmetic obstruction
to the printed step “(5.27)–(5.28) yields (5.26)”. -/
theorem union_bound_does_not_exponentiate :
    ((2 : ℝ) * (1 / 2 : ℝ)) > (1 / 2 : ℝ) ^ 2 := by
  norm_num

/-- Correct scalar core of the repaired bad-event estimate.  A larger total
penalty gives a smaller exponential regulator for nonnegative coupling. -/
theorem bad_event_pointwise_suppression
    (lam penalty threshold : ℝ)
    (hlam : 0 ≤ lam)
    (hpen : threshold ≤ penalty) :
    Real.exp (-(lam * penalty)) ≤ Real.exp (-(lam * threshold)) := by
  have hmul : lam * threshold ≤ lam * penalty :=
    mul_le_mul_of_nonneg_left hpen hlam
  have hneg : -(lam * penalty) ≤ -(lam * threshold) := neg_le_neg hmul
  exact Real.exp_le_exp.mpr hneg

#print axioms union_bound_does_not_exponentiate
#print axioms bad_event_pointwise_suppression

end Millennium.YangMills.FaizalShabirLargeFieldSuppressionRepair
