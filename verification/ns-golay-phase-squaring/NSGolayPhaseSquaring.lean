import Mathlib

/-!
# Golay phase squaring on parent-return paths

This file formalizes only the finite real-sign shadow of the two-step path
algebra:

* an intermediate sign with square one disappears after source and return;
* opposite intermediate signs give the same return weight;
* two positive path coefficients with one fixed nonzero parent sign cannot
  cancel; and
* cancellation requires signed, not merely positive, path coefficients.

It does not formalize complex phases, Fourier packets, helical coefficients,
the Navier--Stokes bilinear operator, shadowing, or blow-up.
-/

namespace NSGolayPhaseSquaring

/-- BANKER: an intermediate binary phase is squared away on a two-step path. -/
theorem intermediate_sign_squared_away
    (parent intermediate : ℝ) (hunit : intermediate ^ 2 = 1) :
    (parent * intermediate) * intermediate = parent := by
  calc
    (parent * intermediate) * intermediate =
        parent * intermediate ^ 2 := by ring
    _ = parent := by rw [hunit]; ring

/-- Opposite intermediate signs produce the same parent-return weight. -/
theorem opposite_intermediate_signs_same_return (parent : ℝ) :
    (parent * 1) * 1 = parent ∧
      (parent * (-1)) * (-1) = parent := by
  constructor <;> ring

/-- BANKER/CRITIC: two strictly positive geometric path coefficients with a
fixed nonzero parent sign add coherently and cannot cancel. -/
theorem fixed_parent_sign_positive_paths_do_not_cancel
    (parent b₁ b₂ : ℝ)
    (hparent : parent ≠ 0) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    parent * b₁ + parent * b₂ ≠ 0 := by
  have hsum : 0 < b₁ + b₂ := add_pos hb₁ hb₂
  have hsum0 : b₁ + b₂ ≠ 0 := ne_of_gt hsum
  calc
    parent * b₁ + parent * b₂ = parent * (b₁ + b₂) := by ring
    _ ≠ 0 := mul_ne_zero hparent hsum0

/-- The minimal two-species Golay counterexample: one positive and one
negative intermediate sign both return positively to the same positive
parent. -/
theorem two_opposite_sign_paths_add_instead_of_cancel :
    ((1 : ℝ) * 1) * 1 + ((1 : ℝ) * (-1)) * (-1) = 2 := by
  norm_num

/-- CLEANER: a two-path scalar cancellation with a nonzero parent factor is
exactly a signed coefficient condition `b₁+b₂=0`; unit intermediate phases
alone do not provide it. -/
theorem two_path_cancellation_iff_signed_coefficients_cancel
    (parent b₁ b₂ : ℝ) (hparent : parent ≠ 0) :
    parent * b₁ + parent * b₂ = 0 ↔ b₁ + b₂ = 0 := by
  constructor
  · intro h
    have hfactor : parent * (b₁ + b₂) = 0 := by
      calc
        parent * (b₁ + b₂) = parent * b₁ + parent * b₂ := by ring
        _ = 0 := h
    exact (mul_eq_zero.mp hfactor).resolve_left hparent
  · intro h
    calc
      parent * b₁ + parent * b₂ = parent * (b₁ + b₂) := by ring
      _ = 0 := by rw [h]; ring

#print axioms intermediate_sign_squared_away
#print axioms opposite_intermediate_signs_same_return
#print axioms fixed_parent_sign_positive_paths_do_not_cancel
#print axioms two_opposite_sign_paths_add_instead_of_cancel
#print axioms two_path_cancellation_iff_signed_coefficients_cancel

end NSGolayPhaseSquaring
