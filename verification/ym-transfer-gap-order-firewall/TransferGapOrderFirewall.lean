import Mathlib

/-!
# Yang--Mills transfer-gap order firewall

Finite scalar cores for auditing transfer-operator gap propagation.

A lower quadratic-form/operator bound on a vacuum-orthogonal transfer sector
controls the transfer eigenvalue from below, whereas preservation of a positive
Hamiltonian gap requires an upper bound on that excited transfer eigenvalue.
The one-dimensional counterexample below records that the direction cannot be
reversed.

The second theorem records the physical-spacing factor under genuine
coarse-graining `a' = b*a`, `b>1`: the coefficient `a/a'` is strictly below
one. Thus an estimate containing `(a/a') * Delta` cannot be weakened to
`>= Delta` without an additional compensating theorem.

No Yang--Mills existence or mass-gap theorem is proved here.
-/

namespace Millennium.YangMills.TransferGapOrderFirewall

/-- On a one-dimensional excited sector, the lower-order relation
`lambda_src <= lambda_dst` is compatible with a positive source transfer gap
and a zero destination transfer gap. This is the exact scalar obstruction to
using a lower operator bound to deduce the upper excited-eigenvalue estimate
needed for gap persistence. -/
theorem lower_transfer_order_can_close_gap :
    let λsrc : ℚ := 1 / 2
    let λdst : ℚ := 1
    λsrc ≤ λdst ∧ 0 < 1 - λsrc ∧ 1 - λdst = 0 := by
  norm_num

/-- The specific upper estimate required for gap persistence does not follow
from the corresponding lower relation, even with zero defect. -/
theorem lower_relation_does_not_force_upper_relation :
    let λsrc : ℚ := 1 / 2
    let λdst : ℚ := 1
    let ε : ℚ := 0
    (λsrc - ε ≤ λdst) ∧ ¬ (λdst ≤ λsrc + ε) := by
  norm_num

/-- Under genuine coarse-graining `a' = b*a` with `b>1`, the spacing ratio
`a/a'` is strictly less than one. -/
theorem coarsening_spacing_ratio_lt_one
    (a b : ℝ) (ha : 0 < a) (hb : 1 < b) :
    a / (b * a) < 1 := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hba : 0 < b * a := mul_pos hb0 ha
  rw [div_lt_iff₀ hba]
  nlinarith

/-- Consequently, multiplying a positive physical gap by `a/(b*a)` strictly
shrinks it. One may not replace this factor by one in a lower bound. -/
theorem coarsening_spacing_factor_shrinks_gap
    (a b Δ : ℝ) (ha : 0 < a) (hb : 1 < b) (hΔ : 0 < Δ) :
    (a / (b * a)) * Δ < Δ := by
  have hratio : a / (b * a) < 1 := coarsening_spacing_ratio_lt_one a b ha hb
  nlinarith [mul_pos (show 0 < a / (b * a) by
    exact div_pos ha (mul_pos (lt_trans (by norm_num) hb) ha)) hΔ]

#print axioms lower_transfer_order_can_close_gap
#print axioms lower_relation_does_not_force_upper_relation
#print axioms coarsening_spacing_ratio_lt_one
#print axioms coarsening_spacing_factor_shrinks_gap

end Millennium.YangMills.TransferGapOrderFirewall
