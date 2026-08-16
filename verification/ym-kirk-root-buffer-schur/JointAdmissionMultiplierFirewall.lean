import Mathlib

/-!
# Joint-admission multiplier firewall

Finite quantifier firewall for the Kirk-v4 Lemma-6.41 admission step.  A row
that can be made arbitrarily small does not by itself control its product with
an otherwise untyped multiplier; one needs the multiplier fixed or uniformly
bounded before taking the small-row limit.

This file does not prove Kirk's compact row, identify the manuscript's `C_E`,
prove Theorem 6.43, construct a Yang--Mills continuum theory, or prove a mass
gap / Clay theorem.
-/

namespace Millennium.YangMills

/-- An arbitrarily small positive row can be paired with a positive multiplier
whose product is exactly one.  Thus `η -> 0` alone cannot justify `C(R)*η(R)
-> 0` when the multiplier is allowed to depend on the same parameter. -/
theorem small_row_does_not_control_untyped_multiplier
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C η : ℝ,
      0 < C ∧ 0 < η ∧ η < ε ∧ C * η = 1 := by
  refine ⟨2 / ε, ε / 2, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · linarith
  · have hne : ε ≠ 0 := ne_of_gt hε
    field_simp [hne]

/-- Positive repair: once the multiplier has one parameter-independent upper
bound `Cmax`, making `Cmax * η` small controls every admitted multiplier
`C <= Cmax`. -/
theorem fixed_multiplier_bound_closes_admission
    {C Cmax η δ : ℝ}
    (hC : C ≤ Cmax) (hη : 0 ≤ η)
    (hsmall : Cmax * η ≤ δ) :
    C * η ≤ δ := by
  exact (mul_le_mul_of_nonneg_right hC hη).trans hsmall

#print axioms small_row_does_not_control_untyped_multiplier
#print axioms fixed_multiplier_bound_closes_admission

end Millennium.YangMills
