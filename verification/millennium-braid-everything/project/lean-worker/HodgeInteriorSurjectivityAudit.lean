import Mathlib

/-!
# Hodge lane: interior-surjectivity audit core

This file formalizes the elementary exact-sequence logic used to audit
A. Mostaed, *Automorphic Cohomology and the Limits of Algebraic Cycles*,
arXiv:2602.06865v1.

It does **not** formalize singular or intersection cohomology, Baily--Borel
compactifications, Shimura varieties, or the Hodge conjecture.

The abstract core is this.  In an exact fragment

`compactSupport --f--> ordinary --g--> boundary`,

if the boundary group in the relevant degree is zero, exactness at `ordinary`
forces `f` to be surjective.  If an equivalence then identifies `ordinary`
with intersection cohomology and defines interior classes as the image of the
composite, every intersection-cohomology class is interior.  A non-interior
class is incompatible with that package of premises.
-/

namespace HodgeInteriorSurjectivityAudit

/-- Exactness followed by a zero target forces the preceding map to be
surjective.  `hexact` is the only part of the long exact sequence needed for
this conclusion. -/
theorem exact_to_zero_forces_surjective
    {CompactSupport Ordinary Boundary : Type*}
    [Zero Boundary]
    (toOrdinary : CompactSupport → Ordinary)
    (toBoundary : Ordinary → Boundary)
    (hBoundaryZero : ∀ b : Boundary, b = 0)
    (hexact : ∀ y : Ordinary,
      toBoundary y = 0 → ∃ x : CompactSupport, toOrdinary x = y) :
    Function.Surjective toOrdinary := by
  intro y
  apply hexact y
  exact hBoundaryZero (toBoundary y)

/-- A bijective ordinary-to-intersection identification transfers the
surjectivity of compactly supported cohomology. -/
theorem equivalence_transfers_surjectivity
    {CompactSupport Ordinary Intersection : Type*}
    (toOrdinary : CompactSupport → Ordinary)
    (ordinaryToIntersection : Ordinary ≃ Intersection)
    (hsurj : Function.Surjective toOrdinary) :
    Function.Surjective
      (fun x => ordinaryToIntersection (toOrdinary x)) := by
  intro z
  obtain ⟨y, hy⟩ := ordinaryToIntersection.surjective z
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨x, ?_⟩
  rw [hx]
  exact hy

/-- Under the two preceding premises, every target class lies in the declared
interior image. -/
theorem every_intersection_class_is_interior
    {CompactSupport Ordinary Boundary Intersection : Type*}
    [Zero Boundary]
    (toOrdinary : CompactSupport → Ordinary)
    (toBoundary : Ordinary → Boundary)
    (ordinaryToIntersection : Ordinary ≃ Intersection)
    (hBoundaryZero : ∀ b : Boundary, b = 0)
    (hexact : ∀ y : Ordinary,
      toBoundary y = 0 → ∃ x : CompactSupport, toOrdinary x = y) :
    ∀ z : Intersection,
      ∃ x : CompactSupport,
        ordinaryToIntersection (toOrdinary x) = z := by
  have hsurj : Function.Surjective toOrdinary :=
    exact_to_zero_forces_surjective
      toOrdinary toBoundary hBoundaryZero hexact
  exact equivalence_transfers_surjectivity
    toOrdinary ordinaryToIntersection hsurj

/-- Consequently, the same package cannot contain a non-interior class. -/
theorem no_noninterior_class_under_stated_package
    {CompactSupport Ordinary Boundary Intersection : Type*}
    [Zero Boundary]
    (toOrdinary : CompactSupport → Ordinary)
    (toBoundary : Ordinary → Boundary)
    (ordinaryToIntersection : Ordinary ≃ Intersection)
    (hBoundaryZero : ∀ b : Boundary, b = 0)
    (hexact : ∀ y : Ordinary,
      toBoundary y = 0 → ∃ x : CompactSupport, toOrdinary x = y) :
    ¬ ∃ z : Intersection,
      ∀ x : CompactSupport,
        ordinaryToIntersection (toOrdinary x) ≠ z := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ := every_intersection_class_is_interior
    toOrdinary toBoundary ordinaryToIntersection
    hBoundaryZero hexact z
  exact (hz x) hx

/-- Real dimension of the symmetric space
`SO(2,26)/(SO(2)×SO(26))`. -/
theorem so_two_twenty_six_real_dimension :
    ((28 : ℤ) * 27) / 2 - 1 - ((26 : ℤ) * 25) / 2 = 52 := by
  norm_num

/-- Its Hermitian complex dimension is `26`, not `13`. -/
theorem so_two_twenty_six_complex_dimension :
    (52 : ℤ) / 2 = 26 := by
  norm_num

/-- Degree 26 lies strictly above the top ordinary cohomological degree of a
finite union of curves and points, once that geometric input is supplied. -/
theorem degree_twenty_six_above_curve_top_degree :
    (2 : ℕ) < 26 := by
  norm_num

#print axioms exact_to_zero_forces_surjective
#print axioms equivalence_transfers_surjectivity
#print axioms every_intersection_class_is_interior
#print axioms no_noninterior_class_under_stated_package
#print axioms so_two_twenty_six_real_dimension
#print axioms so_two_twenty_six_complex_dimension
#print axioms degree_twenty_six_above_curve_top_degree

end HodgeInteriorSurjectivityAudit
