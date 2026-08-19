import Mathlib

/-!
# Massless relative-tail soft-mode firewall

Finite scalar obstruction for a proposed repair of a massless covariance tail.

If a Green factor `1 / λ` is split into a uniformly bounded finite-scale part
`A` and a tail `1 / λ - A`, then for sufficiently soft `λ > 0` the tail carries
an arbitrarily large fraction of the full Green factor.  Thus a uniform strict
relative-form bound on the complete massless long-scale tail cannot follow from
boundedness of the retained finite-scale part alone.

This file does not formalize finite-range decomposition, BKAR, gauge theory,
Osterwalder--Schrader reconstruction, or Yang--Mills.
-/

namespace Millennium.YangMills.MasslessRelativeTailSoftModeFirewall

/-- Algebraic identity for the relative weight of a Green tail. -/
theorem green_tail_relative_identity
    (λ A : ℝ)
    (hλ : 0 < λ) :
    λ * (1 / λ - A) = 1 - λ * A := by
  field_simp [ne_of_gt hλ]
  <;> ring

/-- If the retained finite-scale part is bounded by `M`, every sufficiently
soft mode makes the complementary massless tail exceed any prescribed strict
relative fraction `θ < 1`. -/
theorem soft_mode_defeats_strict_relative_tail
    (λ A M θ : ℝ)
    (hλ : 0 < λ)
    (hA : A ≤ M)
    (hθ : θ < 1)
    (hsoft : λ * M < 1 - θ) :
    θ < λ * (1 / λ - A) := by
  have hmul : λ * A ≤ λ * M :=
    mul_le_mul_of_nonneg_left hA (le_of_lt hλ)
  have hratio := green_tail_relative_identity λ A hλ
  rw [hratio]
  linarith

/-- Equivalent form: under the same soft-mode condition, the tail itself is
larger than `θ` times the full Green factor. -/
theorem soft_mode_tail_gt_fraction_of_green
    (λ A M θ : ℝ)
    (hλ : 0 < λ)
    (hA : A ≤ M)
    (hθ : θ < 1)
    (hsoft : λ * M < 1 - θ) :
    θ * (1 / λ) < 1 / λ - A := by
  have h := soft_mode_defeats_strict_relative_tail λ A M θ hλ hA hθ hsoft
  have hλinv : 0 < 1 / λ := by positivity
  nlinarith [green_tail_relative_identity λ A hλ]

#print axioms green_tail_relative_identity
#print axioms soft_mode_defeats_strict_relative_tail
#print axioms soft_mode_tail_gt_fraction_of_green

end Millennium.YangMills.MasslessRelativeTailSoftModeFirewall
