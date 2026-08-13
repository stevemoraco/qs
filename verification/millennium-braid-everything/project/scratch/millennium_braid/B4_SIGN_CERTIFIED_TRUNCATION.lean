import Mathlib

/-!
# B4 sign-certified truncation core

Finite Lean-ready lemmas for the revived RH finite-Weil/Loewner lane.

The intended dictionary is:
* `qTotal` = cutoff-free Weil/zero-side quadratic form after exact transport;
* `qCut` = finite-cutoff Galerkin quadratic form;
* `qTail` = omitted archimedean Gram tail;
* `V` = the finite evaluation/transport map.

The only structural input used here is that the omitted tail is nonnegative.
No Riemann-Hypothesis statement is asserted.
-/

namespace MillenniumB4
namespace SignCertifiedTruncation

/-- If a cutoff quadratic form and its omitted tail are both nonnegative,
then the cutoff-free form is nonnegative on the transported range. -/
theorem transported_nonnegative
    {α β : Type*}
    (V : α → β)
    (qTotal : β → ℝ)
    (qCut qTail : α → ℝ)
    (htransport : ∀ x, qTotal (V x) = qCut x + qTail x)
    (hcut : ∀ x, 0 ≤ qCut x)
    (htail : ∀ x, 0 ≤ qTail x) :
    ∀ x, 0 ≤ qTotal (V x) := by
  intro x
  rw [htransport x]
  exact add_nonneg (hcut x) (htail x)

/-- With surjective transport, cutoff positivity plus a positive tail proves
nonnegativity of the entire target quadratic form. -/
theorem total_nonnegative_of_surjective_cutoff_tail
    {α β : Type*}
    (V : α → β)
    (qTotal : β → ℝ)
    (qCut qTail : α → ℝ)
    (hV : Function.Surjective V)
    (htransport : ∀ x, qTotal (V x) = qCut x + qTail x)
    (hcut : ∀ x, 0 ≤ qCut x)
    (htail : ∀ x, 0 ≤ qTail x) :
    ∀ y, 0 ≤ qTotal y := by
  intro y
  rcases hV y with ⟨x, rfl⟩
  exact transported_nonnegative V qTotal qCut qTail htransport hcut htail x

/-- A negative cutoff-free direction forces a negative finite-cutoff direction
whenever the omitted tail is nonnegative.  No tail-size estimate is needed. -/
theorem negative_cutoff_of_negative_total
    {α β : Type*}
    (V : α → β)
    (qTotal : β → ℝ)
    (qCut qTail : α → ℝ)
    (hV : Function.Surjective V)
    (htransport : ∀ x, qTotal (V x) = qCut x + qTail x)
    (htail : ∀ x, 0 ≤ qTail x)
    (hneg : ∃ y, qTotal y < 0) :
    ∃ x, qCut x < 0 := by
  rcases hneg with ⟨y, hy⟩
  rcases hV y with ⟨x, rfl⟩
  rw [htransport x] at hy
  exact ⟨x, by linarith [htail x]⟩

/-- Reverse sign certification with an explicit tail budget: if the finite
cutoff Rayleigh value is below minus the maximal omitted-tail contribution,
then negativity survives after restoring the tail. -/
theorem negative_total_of_cutoff_below_budget
    {α : Type*}
    (qCut qTail scale : α → ℝ)
    (B : ℝ)
    (x : α)
    (hcut : qCut x < -(B * scale x))
    (htail : qTail x ≤ B * scale x) :
    qCut x + qTail x < 0 := by
  linarith

/-- Quantitative margin version: a cutoff negativity margin `δ` survives a
bounded positive tail and leaves at least the same algebraic residual margin. -/
theorem negative_total_with_margin
    {α : Type*}
    (qCut qTail scale : α → ℝ)
    (B δ : ℝ)
    (x : α)
    (hδ : 0 < δ)
    (hcut : qCut x ≤ -(B * scale x) - δ)
    (htail : qTail x ≤ B * scale x) :
    qCut x + qTail x < 0 := by
  linarith

end SignCertifiedTruncation
end MillenniumB4
