import Mathlib

/-!
Finite logical core of the Suzuki cofinal-localization criterion.

This does NOT formalize the Weil quadratic form, Suzuki's operator A_a,
or the analytic identification of RH.  It only formalizes the load-bearing
order/cofinality implication used after those analytic facts are imported.
-/

namespace Millennium.RH.CofinalAntitoneCore

/-- An antitone real-valued quantity is nonnegative everywhere on a positive
ray if it is nonnegative on any cofinal sample of that ray. -/
theorem nonneg_everywhere_of_cofinal
    (f : ℝ → ℝ)
    (a : ℕ → ℝ)
    (hf : Antitone f)
    (hcofinal : ∀ x : ℝ, 0 < x → ∃ n : ℕ, x ≤ a n)
    (hsample : ∀ n : ℕ, 0 ≤ f (a n)) :
    ∀ x : ℝ, 0 < x → 0 ≤ f x := by
  intro x hx
  obtain ⟨n, hxn⟩ := hcofinal x hx
  exact le_trans (hsample n) (hf hxn)

/-- If failure of a target statement is equivalent to negativity somewhere,
cofinal nonnegativity of an antitone certificate proves the target. -/
theorem target_of_cofinal_nonneg
    (Target : Prop)
    (f : ℝ → ℝ)
    (a : ℕ → ℝ)
    (hf : Antitone f)
    (hcofinal : ∀ x : ℝ, 0 < x → ∃ n : ℕ, x ≤ a n)
    (hfail : (¬ Target) ↔ ∃ x : ℝ, 0 < x ∧ f x < 0)
    (hsample : ∀ n : ℕ, 0 ≤ f (a n)) :
    Target := by
  by_contra hT
  obtain ⟨x, hx, hneg⟩ := hfail.mp hT
  have hnonneg : 0 ≤ f x :=
    nonneg_everywhere_of_cofinal f a hf hcofinal hsample x hx
  exact (not_lt_of_ge hnonneg) hneg

#print axioms nonneg_everywhere_of_cofinal
#print axioms target_of_cofinal_nonneg

end Millennium.RH.CofinalAntitoneCore
