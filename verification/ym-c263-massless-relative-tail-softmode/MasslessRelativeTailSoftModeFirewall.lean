import Mathlib

/-!
# Massless relative-tail soft-mode firewall

Finite scalar obstruction for a proposed repair of a massless covariance tail.

If a Green factor `1 / lam` is split into a uniformly bounded finite-scale part
`A` and a tail `1 / lam - A`, then sufficiently soft positive `lam` can force
the tail to carry an arbitrarily large relative Green weight. Thus a uniform
strict relative-form bound on the complete massless long-scale tail cannot
follow from boundedness of the retained finite-scale part alone.

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

/-- If the retained finite-scale part is bounded by `M`, every sufficiently
soft mode satisfying the displayed budget makes the complementary massless
tail exceed the prescribed relative level `theta`. -/
theorem soft_mode_defeats_strict_relative_tail
    (lam A M theta : ℝ)
    (hlam : 0 < lam)
    (hA : A ≤ M)
    (hsoft : lam * M < 1 - theta) :
    theta < lam * (1 / lam - A) := by
  have hmul : lam * A ≤ lam * M :=
    mul_le_mul_of_nonneg_left hA (le_of_lt hlam)
  rw [green_tail_relative_identity lam A hlam]
  linarith

#print axioms green_tail_relative_identity
#print axioms soft_mode_defeats_strict_relative_tail

end Millennium.YangMills.MasslessRelativeTailSoftModeFirewall
