import Mathlib

/-!
# Massless relative-tail soft-mode firewall

Finite scalar obstruction for a proposed repair of a massless covariance tail.

If a Green factor `1 / lam` is split into a uniformly bounded finite-scale part
`A` and a tail `1 / lam - A`, then for sufficiently soft `lam > 0` the tail carries
an arbitrarily large fraction of the full Green factor. Thus a uniform strict
relative-form bound on the complete massless long-scale tail cannot follow from
boundedness of the retained finite-scale part alone.

This file does not formalize finite-range decomposition, BKAR, gauge theory,
Osterwalder--Schrader reconstruction, or Yang--Mills.
-/

namespace Millennium.YangMills.MasslessRelativeTailSoftModeFirewall

/-- Algebraic identity for the relative weight of a Green tail. -/
theorem green_tail_relative_identity
    (lam A : ℝ)
    (hlam : 0 < lam) :
    lam * (1 / lam - A) = 1 - lam * A := by
  field_simp [ne_of_gt hlam]
  <;> ring

/-- If the retained finite-scale part is bounded by `M`, every sufficiently
soft mode makes the complementary massless tail exceed any prescribed strict
relative fraction `theta < 1`. -/
theorem soft_mode_defeats_strict_relative_tail
    (lam A M theta : ℝ)
    (hlam : 0 < lam)
    (hA : A ≤ M)
    (htheta : theta < 1)
    (hsoft : lam * M < 1 - theta) :
    theta < lam * (1 / lam - A) := by
  have hmul : lam * A ≤ lam * M :=
    mul_le_mul_of_nonneg_left hA (le_of_lt hlam)
  rw [green_tail_relative_identity lam A hlam]
  linarith

/-- Equivalent form: under the same soft-mode condition, the tail itself is
larger than `theta` times the full Green factor. -/
theorem soft_mode_tail_gt_fraction_of_green
    (lam A M theta : ℝ)
    (hlam : 0 < lam)
    (hA : A ≤ M)
    (htheta : theta < 1)
    (hsoft : lam * M < 1 - theta) :
    theta * (1 / lam) < 1 / lam - A := by
  have h :=
    soft_mode_defeats_strict_relative_tail lam A M theta hlam hA htheta hsoft
  apply (mul_lt_mul_left hlam).mp
  calc
    lam * (theta * (1 / lam)) = theta := by
      field_simp [ne_of_gt hlam]
      <;> ring
    _ < lam * (1 / lam - A) := h

#print axioms green_tail_relative_identity
#print axioms soft_mode_defeats_strict_relative_tail
#print axioms soft_mode_tail_gt_fraction_of_green

end Millennium.YangMills.MasslessRelativeTailSoftModeFirewall
