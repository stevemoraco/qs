import Mathlib

/-!
# Hodge self-square universal reduction

This file formalizes the exact functorial core of the standard reduction

`HC(X × X) ⟹ HC(X)`.

A class `α` on `X` is pulled to the self-square by the first projection. If the
pulled class is represented by a cycle on `X × X`, refined pullback along the
section `X × {x}` returns a cycle on `X` representing `α`.

The geometry, Chow groups, cycle-class maps, refined Gysin pullback, Hodge
bidegrees, smooth projective varieties, and the official Hodge conjecture are
not defined here. They are represented by explicit maps and their two exact
naturality laws.
-/

namespace Millennium.Hodge.SelfSquareUniversalReduction

variable {CycleX CycleXX HX HXX : Type*}

/-- The exact data consumed by the self-square-to-factor reduction. -/
structure SectionPullbackData where
  classX : CycleX → HX
  classXX : CycleXX → HXX
  projectionPull : HX → HXX
  sectionPullClass : HXX → HX
  sectionPullCycle : CycleXX → CycleX
  section_projection : Function.LeftInverse sectionPullClass projectionPull
  cycleClass_naturality :
    ∀ z, sectionPullClass (classXX z) = classX (sectionPullCycle z)

/-- A class lies in the image of the selected cycle-class map. -/
def Algebraic (classMap : CycleX → HX) (α : HX) : Prop :=
  α ∈ Set.range classMap

/--
If the first-projection pullback of `α` is algebraic on the self-square, then
`α` is algebraic on the factor.
-/
theorem algebraic_of_selfSquare_projection_algebraic
    (D : SectionPullbackData (CycleX := CycleX) (CycleXX := CycleXX)
      (HX := HX) (HXX := HXX))
    (α : HX)
    (hsq : D.projectionPull α ∈ Set.range D.classXX) :
    α ∈ Set.range D.classX := by
  rcases hsq with ⟨z, hz⟩
  refine ⟨D.sectionPullCycle z, ?_⟩
  calc
    D.classX (D.sectionPullCycle z) =
        D.sectionPullClass (D.classXX z) :=
      (D.cycleClass_naturality z).symm
    _ = D.sectionPullClass (D.projectionPull α) := by rw [hz]
    _ = α := D.section_projection α

/-- Same theorem in the `Algebraic` wrapper. -/
theorem algebraic_of_selfSquare_projection_algebraic'
    (D : SectionPullbackData (CycleX := CycleX) (CycleXX := CycleXX)
      (HX := HX) (HXX := HXX))
    (α : HX)
    (hsq : Algebraic D.classXX (D.projectionPull α)) :
    Algebraic D.classX α := by
  exact algebraic_of_selfSquare_projection_algebraic D α hsq

/--
A self-square algebraicity theorem for every pulled class gives algebraicity of
all factor classes.
-/
theorem all_factor_classes_of_all_selfSquare_projection_classes
    (D : SectionPullbackData (CycleX := CycleX) (CycleXX := CycleXX)
      (HX := HX) (HXX := HXX))
    (hall : ∀ α : HX, Algebraic D.classXX (D.projectionPull α)) :
    ∀ α : HX, Algebraic D.classX α := by
  intro α
  exact algebraic_of_selfSquare_projection_algebraic' D α (hall α)

/--
Restricted predicates, such as “rational Hodge class of codimension `p`”, pass
through the same reduction once projection pullback preserves the predicate and
the self-square theorem algebraizes every pulled predicate class.
-/
theorem all_predicate_classes_of_selfSquare_theorem
    (D : SectionPullbackData (CycleX := CycleX) (CycleXX := CycleXX)
      (HX := HX) (HXX := HXX))
    (PX : HX → Prop) (PXX : HXX → Prop)
    (hpull : ∀ α, PX α → PXX (D.projectionPull α))
    (hself : ∀ β, PXX β → Algebraic D.classXX β) :
    ∀ α, PX α → Algebraic D.classX α := by
  intro α hα
  apply algebraic_of_selfSquare_projection_algebraic' D α
  exact hself (D.projectionPull α) (hpull α hα)

#print axioms algebraic_of_selfSquare_projection_algebraic
#print axioms algebraic_of_selfSquare_projection_algebraic'
#print axioms all_factor_classes_of_all_selfSquare_projection_classes
#print axioms all_predicate_classes_of_selfSquare_theorem

end Millennium.Hodge.SelfSquareUniversalReduction
