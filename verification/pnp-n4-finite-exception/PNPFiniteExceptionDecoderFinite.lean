import Mathlib

/-!
# PNP unit-image decoder plus finite exceptional images — finite logical core

HONESTY BOUNDARY

This file proves only finite logical composition facts:

* a decoder for one positive family can be OR-combined with a finite set of
  hardwired exceptional image points;
* completeness is preserved for the union;
* acceptance implies collision with some member of the union, provided the
  component decoder and hardwired image set have that property;
* the scalar union-bound budget preserves a `2^{-s}` margin when the positive
  count is at most `2^s` and pairwise collision is at most `2^{-2s}`.

It does NOT formalize the CLY hash family, the UNIT image decoder, circuit size,
probabilistic circuits, fractional transversals, NP, P/poly, or P versus NP.

No `sorry`, `admit`, custom axiom, or result-equivalent placeholder is intended.
-/

namespace Millennium
namespace PVsNP
namespace FiniteExceptionDecoder

variable {X Y : Type*}

/-- A proposition-valued union decoder: use the base image decoder or match one
of finitely many hardwired exceptional image points. -/
def acceptsUnion [DecidableEq Y]
    (baseAccept : Y → Prop) (exceptionalImages : Finset Y) (y : Y) : Prop :=
  baseAccept y ∨ y ∈ exceptionalImages

/-- Every base positive remains accepted. -/
theorem acceptsUnion_of_base
    [DecidableEq Y]
    (hash : X → Y)
    (Base : X → Prop)
    (baseAccept : Y → Prop)
    (exceptionalImages : Finset Y)
    (hbase : ∀ x, Base x → baseAccept (hash x)) :
    ∀ x, Base x →
      acceptsUnion baseAccept exceptionalImages (hash x) := by
  intro x hx
  exact Or.inl (hbase x hx)

/-- Every exceptional positive whose image is hardwired remains accepted. -/
theorem acceptsUnion_of_exception
    [DecidableEq Y]
    (hash : X → Y)
    (Exceptional : X → Prop)
    (baseAccept : Y → Prop)
    (exceptionalImages : Finset Y)
    (hexception : ∀ x, Exceptional x → hash x ∈ exceptionalImages) :
    ∀ x, Exceptional x →
      acceptsUnion baseAccept exceptionalImages (hash x) := by
  intro x hx
  exact Or.inr (hexception x hx)

/-- If each component decoder is sound as an image-collision statement, then
acceptance by their union is sound for the union of positive families. -/
theorem acceptsUnion_implies_positive_collision
    [DecidableEq Y]
    (hash : X → Y)
    (Base Exceptional : X → Prop)
    (baseAccept : Y → Prop)
    (exceptionalImages : Finset Y)
    (hbaseSound : ∀ y, baseAccept y →
      ∃ p, Base p ∧ y = hash p)
    (hexceptionSound : ∀ y ∈ exceptionalImages,
      ∃ p, Exceptional p ∧ y = hash p) :
    ∀ x,
      acceptsUnion baseAccept exceptionalImages (hash x) →
      ∃ p, (Base p ∨ Exceptional p) ∧ hash x = hash p := by
  intro x hx
  rcases hx with hbase | hexception
  · obtain ⟨p, hp, hcollision⟩ := hbaseSound (hash x) hbase
    exact ⟨p, Or.inl hp, hcollision⟩
  · obtain ⟨p, hp, hcollision⟩ :=
      hexceptionSound (hash x) hexception
    exact ⟨p, Or.inr hp, hcollision⟩

/-- Scalar source-error budget. If the number of positives is at most `2^s`
and every pair collision has probability at most `1/(2^s)^2`, then the union
bound is at most `1/2^s`. -/
theorem source_exact_union_budget
    (positiveCount : ℕ) (s : ℕ)
    (hcount : positiveCount ≤ 2 ^ s) :
    (positiveCount : ℝ) / ((2 : ℝ) ^ s) ^ 2 ≤
      1 / (2 : ℝ) ^ s := by
  have hpow : 0 < (2 : ℝ) ^ s := by positivity
  have hcountReal : (positiveCount : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast hcount
  apply (div_le_iff₀ (sq_pos_of_pos hpow)).2
  calc
    (positiveCount : ℝ) ≤ (2 : ℝ) ^ s := hcountReal
    _ = (1 / (2 : ℝ) ^ s) * ((2 : ℝ) ^ s) ^ 2 := by
      field_simp [ne_of_gt hpow]

/-- Adding a bounded exceptional-image equality layer to a base decoder with
cost `baseCost` and image length `ell` has the finite gate-count budget shown
below. The complexity theorem separately supplies asymptotic bounds. -/
theorem finite_exception_cost_budget
    (hashCost baseCost ell q finalCost totalCost : ℕ)
    (heq : totalCost = hashCost + baseCost + q * (2 * ell) + finalCost) :
    totalCost ≤ hashCost + baseCost + q * (2 * ell) + finalCost := by
  omega

#print axioms Millennium.PVsNP.FiniteExceptionDecoder.acceptsUnion_of_base
#print axioms Millennium.PVsNP.FiniteExceptionDecoder.acceptsUnion_of_exception
#print axioms Millennium.PVsNP.FiniteExceptionDecoder.acceptsUnion_implies_positive_collision
#print axioms Millennium.PVsNP.FiniteExceptionDecoder.source_exact_union_budget
#print axioms Millennium.PVsNP.FiniteExceptionDecoder.finite_exception_cost_budget

end FiniteExceptionDecoder
end PVsNP
end Millennium
