import Mathlib

/-!
# Finite counterexample to the union-support => pure-branch inference

This is the elementary logical obstruction used in the B3 audit of
Shahmurov, arXiv:2605.09797v2, Theorem 18.4 Step 4.

It does NOT say that an actual Navier--Stokes active-frame measure with mixed
support exists. It proves only that compactness/disjointness plus support in a
union cannot, by itself, imply support in one component. A separate PDE purity
theorem is required.
-/

namespace Millennium.NavierStokes

private def A : Set Bool := {false}
private def B : Set Bool := {true}

/-- Two disjoint closed/finite components can have a support set contained in
    their union while the support is contained in neither component. -/
theorem disjoint_union_support_does_not_force_purity :
    Disjoint A B ∧
      (Set.univ : Set Bool) ⊆ A ∪ B ∧
      ¬ ((Set.univ : Set Bool) ⊆ A) ∧
      ¬ ((Set.univ : Set Bool) ⊆ B) := by
  constructor
  · simp [A, B, Set.disjoint_left]
  constructor
  · intro x hx
    cases x <;> simp [A, B]
  constructor
  · intro h
    have ht : true ∈ A := h (by simp)
    simpa [A] using ht
  · intro h
    have hf : false ∈ B := h (by simp)
    simpa [B] using hf

end Millennium.NavierStokes
