import Mathlib

/-!
# Finite set-theoretic core of the secant-intersection fatal audit

The geometric input is that an embedded variety is contained in each of its
positive secant varieties.  This file formalizes the immediate set-theoretic
consequence.  It does not formalize projective varieties, secant schemes,
intersection theory, Chern characters, Kuga--Satake, or the Hodge conjecture.
-/

namespace Hodge
namespace SecantIntersectionFatal

variable {α : Type*}

/-- If `Y` is contained in its proposed secant locus `Σ`, then their
intersection is exactly `Y`, not a positive-codimension subset of `Y`. -/
theorem intersection_eq_self
    (Y Σ : Set α) (h : Y ⊆ Σ) :
    Σ ∩ Y = Y := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h hx, hx⟩

/-- Equivalent orientation of the same fatal containment. -/
theorem self_intersection_eq_self
    (Y Σ : Set α) (h : Y ⊆ Σ) :
    Y ∩ Σ = Y := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, h hx⟩

/-- A purported proper intersection is incompatible with containment. -/
theorem not_proper_intersection
    (Y Σ : Set α) (h : Y ⊆ Σ) :
    ¬ (Σ ∩ Y ⊂ Y) := by
  rw [intersection_eq_self Y Σ h]
  exact fun hproper => hproper.ne rfl

/-- One vector cannot generate two explicitly independent coordinate
vectors over the rationals.  This is the finite linear-algebra shadow of the
one-class-versus-two-dimensional-Weil-space error. -/
theorem one_rational_line_does_not_contain_both_axes
    (a b : ℚ)
    (h1 : a * (1 : ℚ) = 1 ∧ a * 0 = 0)
    (h2 : b * (1 : ℚ) = 0 ∧ b * 0 = 1) :
    False := by
  norm_num at h2

end SecantIntersectionFatal
end Hodge
