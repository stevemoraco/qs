import Mathlib

/-!
# Hodge: secant-intersection and principal-polarisation firewalls

This file isolates two finite/set-theoretic obstructions to a claimed relative
secant-cycle proof of the Hodge conjecture.

1. If a subspace `Y` is contained in a proposed secant locus `Σ`, then
   `Σ ∩ Y = Y`; the intersection cannot acquire positive codimension merely by
   invoking an expected-dimension theorem.
2. A one-point ambient space cannot contain an embedded two-point source.  This
   is the finite core of the fact that a positive-dimensional abelian variety
   cannot be embedded in `P^0` by a principal polarisation with one section.

The file does not formalize projective geometry, secant schemes, polarised
abelian varieties, Fourier--Mukai transforms, Chow groups, or the Hodge
conjecture.
-/

namespace Millennium.Hodge.SecantIntersectionFirewall

/-- A set contained in another set is unchanged by intersecting with it. -/
theorem intersection_eq_of_contained
    {α : Type*} {Y Σ : Set α} (h : Y ⊆ Σ) :
    Σ ∩ Y = Y := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨h hx, hx⟩

/-- Finite-cardinality form of the same containment firewall. -/
theorem finite_intersection_card_eq_of_contained
    {α : Type*} [DecidableEq α]
    {Y Σ : Finset α} (h : Y ⊆ Σ) :
    (Σ ∩ Y).card = Y.card := by
  have hEq : Σ ∩ Y = Y := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨h hx, hx⟩
  rw [hEq]

/-- If the intersection has the same dimension as `Y`, its codimension inside
`Y` is zero. -/
theorem contained_intersection_codim_zero (dimY : ℕ) :
    dimY - dimY = 0 := by
  omega

/-- Codimension zero cannot equal a positive proposed codimension. -/
theorem zero_codim_not_positive {n : ℕ} (hn : 0 < n) :
    (0 : ℕ) ≠ n := by
  omega

/-- There is no injective map from a two-point type into a one-point type. -/
theorem no_bool_embedding_into_fin_one :
    ¬ ∃ f : Bool → Fin 1, Function.Injective f := by
  rintro ⟨f, hf⟩
  have himage : f false = f true := Subsingleton.elim _ _
  have hfalse : (false : Bool) = true := hf himage
  exact (by decide : (false : Bool) ≠ true) hfalse

/-- Exact ambient-dimension arithmetic: one section gives projective dimension
zero. -/
theorem one_section_projective_dimension_zero :
    1 - 1 = (0 : ℕ) := by
  norm_num

/-- Combining the one-section ledger with the two-point obstruction. -/
theorem principal_one_section_cannot_embed_two_points
    (N : ℕ) (hN : N = 1) :
    N - 1 = 0 ∧
    ¬ ∃ f : Bool → Fin N, Function.Injective f := by
  subst N
  exact ⟨one_section_projective_dimension_zero,
    no_bool_embedding_into_fin_one⟩

#print axioms intersection_eq_of_contained
#print axioms finite_intersection_card_eq_of_contained
#print axioms contained_intersection_codim_zero
#print axioms zero_codim_not_positive
#print axioms no_bool_embedding_into_fin_one
#print axioms one_section_projective_dimension_zero
#print axioms principal_one_section_cannot_embed_two_points

end Millennium.Hodge.SecantIntersectionFirewall
