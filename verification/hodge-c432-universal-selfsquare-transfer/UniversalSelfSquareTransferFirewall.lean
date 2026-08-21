import Mathlib

/-!
# Hodge C432 — universal self-square transfer and K3-correspondence firewall

This file formalizes only the range/functoriality logic used by the human
C432 theorem. It does not define smooth projective varieties, cycle class maps,
K3 surfaces, Hodge structures, or the Hodge conjecture.

The main results say:

* a cycle-compatible left retract transfers algebraicity from the source to the
  target;
* this is the abstract push-pull core of the universal self-square reduction;
* a class-by-class factorization through an algebraic correspondence is
  equivalent to algebraicity of the target class once the model contains the
  trivial product correspondence;
* a bare Hodge/vector-space retract without cycle compatibility does not
  transfer algebraicity, by an exact Boolean countermodel.
-/

noncomputable section

namespace Millennium.Hodge.C432

/-- A class is algebraic when it lies in the range of the chosen cycle map. -/
def Algebraic {Cycle H : Type*} (cl : Cycle → H) (x : H) : Prop :=
  x ∈ Set.range cl

/--
A class-level retract whose projection is compatible with the cycle ranges.
Geometrically, `embed` is the self-square exterior-product map, `project` is
proper pushforward, and `pushCycle` is cycle pushforward.
-/
structure AlgebraicRetract
    (CycleX CycleY HX HY : Type*) where
  clX : CycleX → HX
  clY : CycleY → HY
  embed : HX → HY
  project : HY → HX
  pushCycle : CycleY → CycleX
  leftInverse : Function.LeftInverse project embed
  project_cl : ∀ z, project (clY z) = clX (pushCycle z)

@[simp] theorem AlgebraicRetract.recovers
    {CycleX CycleY HX HY : Type*}
    (R : AlgebraicRetract CycleX CycleY HX HY) (x : HX) :
    R.project (R.embed x) = x :=
  R.leftInverse x

/--
A cycle-compatible retract transfers the algebraicity of every source Hodge
class to every target Hodge class carried into the source.
-/
theorem algebraicity_transfer
    {CycleX CycleY HX HY : Type*}
    (R : AlgebraicRetract CycleX CycleY HX HY)
    {HodgeX : HX → Prop} {HodgeY : HY → Prop}
    (sourceHC : ∀ y, HodgeY y → Algebraic R.clY y)
    (embedHodge : ∀ x, HodgeX x → HodgeY (R.embed x))
    {x : HX} (hx : HodgeX x) :
    Algebraic R.clX x := by
  have hy : Algebraic R.clY (R.embed x) :=
    sourceHC (R.embed x) (embedHodge x hx)
  rcases hy with ⟨z, hz⟩
  refine ⟨R.pushCycle z, ?_⟩
  calc
    R.clX (R.pushCycle z) = R.project (R.clY z) :=
      (R.project_cl z).symm
    _ = R.project (R.embed x) := by rw [hz]
    _ = x := R.leftInverse x

/--
The self-square push-pull core, stated separately to make the intended use
explicit. The geometric instantiation takes `embed α = pr₁* α cup pr₂* [pt]`
and `project = (pr₁)_*`.
-/
theorem selfSquare_hodge_transfer
    {CycleX CycleXX HX HXX : Type*}
    (R : AlgebraicRetract CycleX CycleXX HX HXX)
    {HodgeX : HX → Prop} {HodgeXX : HXX → Prop}
    (selfSquareHC : ∀ y, HodgeXX y → Algebraic R.clY y)
    (externalProductIsHodge : ∀ x, HodgeX x → HodgeXX (R.embed x))
    {x : HX} (hx : HodgeX x) :
    Algebraic R.clX x :=
  algebraicity_transfer R selfSquareHC externalProductIsHodge hx

/--
An abstract model of class-by-class factorization through algebraic
correspondences. `corrOfCycle` is the trivial product correspondence used in
the reverse implication.
-/
structure ClasswiseFactorization
    (CycleX CycleY Corr HX HY : Type*) where
  clX : CycleX → HX
  clY : CycleY → HY
  act : Corr → HY → HX
  baseCycle : CycleY
  corrOfCycle : CycleX → Corr
  corrOfCycle_action :
    ∀ z, act (corrOfCycle z) (clY baseCycle) = clX z
  algebraic_action :
    ∀ Γ y, Algebraic clY y → Algebraic clX (act Γ y)

/--
Exact no-free-lunch theorem: once the model includes the trivial product
correspondence and algebraic correspondences preserve cycle ranges, admitting a
class-by-class factorization is equivalent to the target class already being
algebraic.
-/
theorem classwise_factorization_iff_algebraic
    {CycleX CycleY Corr HX HY : Type*}
    (M : ClasswiseFactorization CycleX CycleY Corr HX HY)
    (x : HX) :
    Algebraic M.clX x ↔
      ∃ Γ y, Algebraic M.clY y ∧ M.act Γ y = x := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨M.corrOfCycle z, M.clY M.baseCycle, ?_, ?_⟩
    · exact ⟨M.baseCycle, rfl⟩
    · exact M.corrOfCycle_action z
  · rintro ⟨Γ, y, hy, hxy⟩
    rw [← hxy]
    exact M.algebraic_action Γ y hy

/-- Target cycle map for the bare-retract countermodel. -/
def boolTargetClass (_ : Unit) : Bool := false

/-- Source cycle map for the bare-retract countermodel. -/
def boolSourceClass (b : Bool) : Bool := b

/--
A bare identity retract of the underlying class spaces can coexist with a
surjective source cycle map and a nonsurjective target cycle map. Therefore a
Hodge/vector-space retract without cycle compatibility proves no algebraicity
transfer.
-/
theorem hodge_retract_alone_countermodel :
    Function.LeftInverse (fun b : Bool => b) (fun b : Bool => b) ∧
      (∀ y : Bool, Algebraic boolSourceClass y) ∧
      ¬ Algebraic boolTargetClass true := by
  constructor
  · intro b
    rfl
  constructor
  · intro y
    exact ⟨y, rfl⟩
  · simp [Algebraic, boolTargetClass]

#print axioms AlgebraicRetract.recovers
#print axioms algebraicity_transfer
#print axioms selfSquare_hodge_transfer
#print axioms classwise_factorization_iff_algebraic
#print axioms hodge_retract_alone_countermodel

end Millennium.Hodge.C432
