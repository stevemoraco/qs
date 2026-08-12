import Mathlib

/-!
# Round 210 Hodge zero-defect finite cores

HONESTY BOUNDARY:

This file formalizes only an abstract finite-expression range-preservation
argument and two logical countermodels. It does not formalize smooth projective
varieties, Hodge structures, André motives, Chow groups, algebraic cycles,
Lefschetz operators, or the Hodge conjecture.
-/

namespace Millennium
namespace Round210Hodge

/-- A finite acyclic presentation syntax with algebraic leaves, unary
operations, and binary operations. -/
inductive Presentation (Leaf Unary Binary : Type*) where
  | leaf : Leaf → Presentation Leaf Unary Binary
  | unary : Unary → Presentation Leaf Unary Binary → Presentation Leaf Unary Binary
  | binary : Binary → Presentation Leaf Unary Binary →
      Presentation Leaf Unary Binary → Presentation Leaf Unary Binary

namespace Presentation

/-- Evaluate a finite presentation in an arbitrary target type. -/
def eval {Leaf Unary Binary V : Type*}
    (leafValue : Leaf → V)
    (unaryValue : Unary → V → V)
    (binaryValue : Binary → V → V → V) :
    Presentation Leaf Unary Binary → V
  | .leaf i => leafValue i
  | .unary op p => unaryValue op (eval leafValue unaryValue binaryValue p)
  | .binary op p q =>
      binaryValue op (eval leafValue unaryValue binaryValue p)
        (eval leafValue unaryValue binaryValue q)

/-- If every leaf is algebraic and every operation preserves the algebraic
range, then every finite zero-defect presentation evaluates to an algebraic
class. This is only the abstract induction skeleton of the conditional support
theorem. -/
theorem eval_mem_algebraic
    {Leaf Unary Binary V : Type*}
    (algebraic : Set V)
    (leafValue : Leaf → V)
    (unaryValue : Unary → V → V)
    (binaryValue : Binary → V → V → V)
    (hleaf : ∀ i, leafValue i ∈ algebraic)
    (hunary : ∀ op x, x ∈ algebraic → unaryValue op x ∈ algebraic)
    (hbinary : ∀ op x y, x ∈ algebraic → y ∈ algebraic →
      binaryValue op x y ∈ algebraic)
    (p : Presentation Leaf Unary Binary) :
    eval leafValue unaryValue binaryValue p ∈ algebraic := by
  induction p with
  | leaf i =>
      exact hleaf i
  | unary op p ih =>
      exact hunary op _ ih
  | binary op p q ihp ihq =>
      exact hbinary op _ _ ihp ihq

end Presentation

/-- Algebraic-range preservation is stable under composition. -/
theorem algebraic_correspondence_composition
    {A B C : Type*}
    (algebraicA : Set A) (algebraicB : Set B) (algebraicC : Set C)
    (f : A → B) (g : B → C)
    (hf : ∀ x, x ∈ algebraicA → f x ∈ algebraicB)
    (hg : ∀ y, y ∈ algebraicB → g y ∈ algebraicC) :
    ∀ x, x ∈ algebraicA → g (f x) ∈ algebraicC := by
  intro x hx
  exact hg (f x) (hf x hx)

/-- The safe inclusions `algebraic ⊆ motivated ⊆ Hodge` do not logically imply
the reverse inclusion `Hodge ⊆ motivated`. -/
theorem safe_inclusions_do_not_reverse :
    ∃ (U : Type) (Algebraic Motivated Hodge : Set U),
      Algebraic ⊆ Motivated ∧ Motivated ⊆ Hodge ∧ ¬ Hodge ⊆ Motivated := by
  refine ⟨Bool, {b | b = false}, {b | b = false}, Set.univ, ?_, ?_, ?_⟩
  · intro b hb
    exact hb
  · intro b hb
    simp
  · intro hreverse
    have hbad : (true : Bool) = false := hreverse (by simp)
    simp at hbad

/-- Finiteness of a defect set alone does not supply a lowering move for every
defect. A one-edge finite countermodel already refutes that implication. -/
theorem finiteness_does_not_supply_lowerability :
    ∃ (E : Type) (_ : Fintype E) (Lowerable : E → Prop),
      ¬ ∀ e, Lowerable e := by
  refine ⟨Fin 1, inferInstance, fun _ => False, ?_⟩
  simp

#print axioms Presentation.eval_mem_algebraic
#print axioms algebraic_correspondence_composition
#print axioms safe_inclusions_do_not_reverse
#print axioms finiteness_does_not_supply_lowerability

end Round210Hodge
end Millennium
