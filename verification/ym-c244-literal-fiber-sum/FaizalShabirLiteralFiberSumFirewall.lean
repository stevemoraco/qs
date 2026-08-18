import Mathlib

/-!
# Faizal--Shabir literal fiber-sum firewall

Finite arithmetic only.  This file formalizes two load-bearing shadows of the
source audit of arXiv:2606.19362v1, Definition 10.1 / Lemma 10.2, Eqs.
(10.13)--(10.18):

* an unweighted sum over `n` equal-size fiber contributions carries an exact
  factor `n` relative to a unit sup input;
* mere finiteness of a block-size-dependent prefactor cannot justify the step
  "increase b until c*(b) b^-2 < 1": the finite choice c*(b)=b^2 exactly
  cancels the engineering factor b^-2.

This does NOT formalize polymer activities, the actual `B_b` map, the source's
Banach norms, Yang--Mills, AF/IR identification, a mass gap, or a Clay theorem.
-/

namespace Millennium.YangMills.FaizalShabirLiteralFiberSumFirewall

open scoped BigOperators

/-- A literal unweighted fiber sum of `n` unit contributions has size `n`.
This is the finite shadow of the total-fiber triangle inequality printed in
Eq. (10.13), not a claim about the true optimal reblocking norm. -/
theorem constant_fiber_sum_eq_card (n : ℕ) :
    (∑ _i in Finset.range n, (1 : ℝ)) = n := by
  simp

/-- In four Euclidean dimensions, a literal unit-weight sum over `b^4`
coherent singleton contributions carries the factor `b^4`. -/
theorem four_dimensional_literal_singleton_sum (b : ℕ) :
    (∑ _i in Finset.range (b ^ 4), (1 : ℝ)) = b ^ 4 := by
  simp

/-- A finite `b`-dependent prefactor can exactly cancel the dimension-six
engineering gain `b^-2`; pointwise finiteness therefore does not imply that
large `b` yields strict contraction. -/
theorem finite_prefactor_can_cancel_dim6_gain (b : ℝ) (hb : b ≠ 0) :
    (b ^ 2) * (1 / (b ^ 2)) = 1 := by
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  field_simp

/-- The literal four-volume factor followed by a separately charged
engineering factor `b^-2` leaves `b^2`. -/
theorem literal_four_volume_then_dim6_gain (b : ℝ) (hb : b ≠ 0) :
    (b ^ 4) * (1 / (b ^ 2)) = b ^ 2 := by
  field_simp
  ring

/-- Dyadic witness: `2^4 * 2^-2 = 4`, not a contraction. -/
theorem dyadic_literal_ledger :
    ((2 : ℝ) ^ 4) * (1 / ((2 : ℝ) ^ 2)) = 4 := by
  norm_num

#print axioms constant_fiber_sum_eq_card
#print axioms four_dimensional_literal_singleton_sum
#print axioms finite_prefactor_can_cancel_dim6_gain
#print axioms literal_four_volume_then_dim6_gain
#print axioms dyadic_literal_ledger

end Millennium.YangMills.FaizalShabirLiteralFiberSumFirewall
